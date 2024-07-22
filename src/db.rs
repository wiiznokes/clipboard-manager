use alive_lock_file::LockFileState;
use cosmic::{
    iced::{subscription, Subscription},
    iced_sctk::util,
};
use derivative::Derivative;
use notify::Watcher;
use std::{
    borrow::Cow,
    collections::{BTreeMap, HashMap},
    fmt::{Debug, Display},
    fs::{self, DirBuilder, File, OpenOptions},
    hash::{DefaultHasher, Hash, Hasher},
    io::{self, Read, Write},
    path::{Path, PathBuf},
    sync::mpsc,
    thread::{self, sleep},
    time::Duration,
};

use anyhow::{anyhow, bail, Result};
use nucleo::{
    pattern::{Atom, AtomKind, CaseMatching, Normalization},
    Matcher, Utf32Str,
};

use chrono::Utc;
use mime::Mime;
use rusqlite::{
    ffi::sqlite3, named_params, params, Connection, ErrorCode, OpenFlags, OptionalExtension, Row,
};

use crate::{
    app::{APP, APPID, ORG, QUALIFIER},
    config::Config,
    message::AppMessage,
    utils::{self, remove_dir_contents},
};

use cached::proc_macro::cached;

type TimeId = i64;

const DB_VERSION: &str = "3";
const DB_PATH: &str = constcat::concat!(APPID, "-db-", DB_VERSION, ".sqlite");

const LOCK_FILE: &str = constcat::concat!(APPID, "/db.lock");
const MODIF_FILE: &str = constcat::concat!(APPID, "/db.modif");

// warning: if you change somethings in here, change the db version
#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Eq)]
pub struct Entry {
    #[derivative(PartialEq = "ignore")]
    #[derivative(Hash = "ignore")]
    pub creation: TimeId,

    #[derivative(PartialEq = "ignore")]
    #[derivative(Hash = "ignore")]
    pub mime: String,

    // todo: lazelly load image in memory, since we can't search them anyways
    pub content: Vec<u8>,

    #[derivative(PartialEq = "ignore")]
    #[derivative(Hash = "ignore")]
    /// (Mime, Content)
    pub metadata: Option<(String, String)>,
}

impl Entry {
    fn get_hash(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    pub fn new(
        creation: i64,
        mime: String,
        content: Vec<u8>,
        metadata: Option<(String, String)>,
    ) -> Self {
        Self {
            creation,
            mime,
            content,
            metadata,
        }
    }

    pub fn new_now(mime: String, content: Vec<u8>, metadata: Option<(String, String)>) -> Self {
        Self::new(Utc::now().timestamp_millis(), mime, content, metadata)
    }

    /// SELECT creation, mime, content, metadataMime, metadata
    fn from_row(row: &Row) -> rusqlite::Result<Self> {
        Ok(Entry::new(
            row.get(0)?,
            row.get(1)?,
            row.get(2)?,
            row.get(3)
                .ok()
                .map(|metadata_mime| (metadata_mime, row.get(4).unwrap())),
        ))
    }
}

impl Debug for Entry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Data")
            .field("creation", &self.creation)
            .field("mime", &self.mime)
            .field("content", &self.get_content())
            .field("metadata", &self.metadata)
            .finish()
    }
}

pub enum Content<'a> {
    Text(&'a str),
    Image(&'a Vec<u8>),
    UriList(Vec<&'a str>),
}

impl Debug for Content<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Text(arg0) => f.debug_tuple("Text").field(arg0).finish(),
            Self::UriList(arg0) => f.debug_tuple("UriList").field(arg0).finish(),
            Self::Image(_) => f.debug_tuple("Image").finish(),
        }
    }
}

impl Entry {
    pub fn get_content(&self) -> Result<Content<'_>> {
        if self.mime == "text/uri-list" {
            let text = if let Some(metadata) = &self.metadata {
                &metadata.1
            } else {
                core::str::from_utf8(&self.content)?
            };

            let uris = text
                .lines()
                .filter(|l| !l.is_empty() && !l.starts_with('#'))
                .collect();

            return Ok(Content::UriList(uris));
        }
        if self.mime.starts_with("text/") {
            return Ok(Content::Text(core::str::from_utf8(&self.content)?));
        }

        if self.mime.starts_with("image/") {
            return Ok(Content::Image(&self.content));
        }

        bail!("unsupported mime type {}", self.mime)
    }

    fn get_searchable_text(&self) -> Option<&str> {
        if self.mime.starts_with("text/") {
            return core::str::from_utf8(&self.content).ok();
        }

        if let Some((mime, metadata)) = &self.metadata {
            #[allow(clippy::assigning_clones)]
            if mime == "text/html" {
                if let Some(alt) = find_alt(metadata) {
                    return Some(alt);
                }
            }
            return Some(metadata);
        }

        None
    }
}

// currently best effort
fn find_alt(html: &str) -> Option<&str> {
    const DEB: &str = "alt=\"";

    if let Some(pos) = html.find(DEB) {
        const OFFSET: usize = DEB.as_bytes().len();

        if let Some(pos_end) = html[pos + OFFSET..].find('"') {
            return Some(&html[pos + OFFSET..pos + pos_end + OFFSET]);
        }
    }

    None
}

pub struct Db {
    conn: Connection,
    hashs: HashMap<u64, TimeId>,
    state: BTreeMap<TimeId, Entry>,
    filtered: Vec<(TimeId, Vec<u32>)>,
    query: String,
    needle: Option<Atom>,
    matcher: Matcher,
    lock: LockFileState,
    runtime_id: u32,
    runtime_path: PathBuf,
}

impl Debug for Db {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Db")
            .field("lock", &self.lock)
            .field("runtime_id", &self.runtime_id)
            .field("runtime_path", &self.runtime_path)
            .finish()
    }
}

impl Db {
    fn notify_modif(&self) -> Result<()> {
        debug!("notify_modif: {}", self.runtime_id);
        let mut f = utils::create_file_all(self.runtime_path.join(MODIF_FILE))?;
        f.write_all(&self.runtime_id.to_ne_bytes())?;

        // todo: remove this assertion
        let mut v = Vec::new();
        File::open(self.runtime_path.join(MODIF_FILE))
            .unwrap()
            .read_to_end(&mut v)
            .unwrap();

        assert_eq!(&v, &self.runtime_id.to_ne_bytes());
        Ok(())
    }

    pub fn update(&mut self, msg: DbMessage) -> Result<()> {
        debug!("{:?}", msg);

        match msg {
            DbMessage::DbWasWritten(id) => {
                if id != self.runtime_id {
                    self.reload()?;
                }
            }
            DbMessage::LockWasRemoved => {
                self.lock = LockFileState::try_lock(LOCK_FILE)?;
            }
        };

        Ok(())
    }

    fn reload(&mut self) -> Result<()> {
        self.hashs.clear();
        self.state.clear();

        let query_load_table = r#"
            SELECT creation, mime, content, metadataMime, metadata
            FROM ClipboardEntries
        "#;

        {
            let mut stmt = self.conn.prepare(query_load_table)?;

            let mut rows = stmt.query(())?;

            while let Some(row) = rows.next()? {
                let data = Entry::from_row(row)?;

                self.hashs.insert(data.get_hash(), data.creation);
                self.state.insert(data.creation, data);
            }
        }

        self.search();
        Ok(())
    }

    pub fn new(config: &Config) -> Result<Self> {
        let directories = directories::ProjectDirs::from(QUALIFIER, ORG, APP).unwrap();

        std::fs::create_dir_all(directories.cache_dir())?;

        Self::inner_new(config, directories.cache_dir())
    }

    fn inner_new(config: &Config, db_dir: &Path) -> Result<Self> {
        let db_path = db_dir.join(DB_PATH);

        if !db_path.exists() {
            remove_dir_contents(db_dir);

            let conn = Connection::open_with_flags(
                db_path,
                OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE,
            )?;

            let query_create_table = r#"
                CREATE TABLE ClipboardEntries (
                    creation INTEGER PRIMARY KEY,
                    mime TEXT NOT NULL,
                    content BLOB NOT NULL,
                    metadataMime TEXT,
                    metadata TEXT,
                    CHECK ((metadataMime IS NULL AND metadata IS NULL) OR (metadataMime IS NOT NULL AND metadata IS NOT NULL))
                )
            "#;

            conn.execute(query_create_table, ())?;

            return Ok(Db {
                conn,
                hashs: HashMap::default(),
                state: BTreeMap::default(),
                filtered: Vec::default(),
                query: String::default(),
                needle: None,
                matcher: Matcher::new(nucleo::Config::DEFAULT),
                lock: LockFileState::try_lock(LOCK_FILE)?,
                runtime_id: rand::random(),
                runtime_path: directories::BaseDirs::new()
                    .unwrap()
                    .runtime_dir()
                    .unwrap()
                    .to_owned(),
            });
        }

        let conn = Connection::open_with_flags(db_path, OpenFlags::SQLITE_OPEN_READ_WRITE)?;

        if let Some(max_duration) = &config.maximum_entries_lifetime {
            let query_delete_old_one = r#"
                DELETE FROM ClipboardEntries
                WHERE (:now - creation) >= :max;
            "#;

            conn.execute(
                query_delete_old_one,
                named_params! {
                    ":now": utils::now_millis(),
                    ":max": max_duration.as_millis().try_into().unwrap_or(u64::MAX),
                },
            )?;
        }

        if let Some(max_number_of_entries) = &config.maximum_entries_number {
            let query_delete_old_one = r#"
                DELETE FROM ClipboardEntries 
                WHERE creation NOT IN
                    (SELECT creation FROM ClipboardEntries
                    ORDER BY creation DESC
                    LIMIT :max_number_of_entries);
            "#;

            conn.execute(
                query_delete_old_one,
                named_params! {
                    ":max_number_of_entries": max_number_of_entries,
                },
            )?;
        }

        let mut db = Db {
            conn,
            hashs: HashMap::default(),
            state: BTreeMap::default(),
            filtered: Vec::default(),
            query: String::default(),
            needle: None,
            matcher: Matcher::new(nucleo::Config::DEFAULT),
            lock: LockFileState::try_lock(LOCK_FILE)?,
            runtime_id: rand::random(),
            runtime_path: directories::BaseDirs::new()
                .unwrap()
                .runtime_dir()
                .unwrap()
                .to_owned(),
        };

        db.reload()?;
        Ok(db)
    }

    fn get_last_row(&mut self) -> Result<Option<Entry>> {
        let query_get_last_row = r#"
            SELECT creation, mime, content, metadataMime, metadata
            FROM ClipboardEntries
            ORDER BY creation DESC
            LIMIT 1
        "#;

        let data = self
            .conn
            .query_row(query_get_last_row, (), Entry::from_row)
            .optional()?;

        Ok(data)
    }

    // the <= 200 condition, is to unsure we reuse the same timestamp
    // of the first process that inserted the data.
    pub fn insert(&mut self, mut data: Entry) -> Result<()> {
        let data_hash = data.get_hash();

        if let Some(old_id) = self.hashs.remove(&data_hash) {
            self.state.remove(&old_id);

            if self.lock.has_lock() {
                let query_delete_old_id = r#"
                    DELETE FROM ClipboardEntries
                    WHERE creation = ?1;
                "#;

                self.conn.execute(query_delete_old_id, [old_id])?;
            }
        }

        if self.lock.has_lock() {
            let query_insert = r#"
            INSERT INTO ClipboardEntries (creation, mime, content, metadataMime, metadata)
            SELECT :new_id, :new_mime, :new_content, :new_metadata_mime, :new_metadata;
        "#;

            if let Err(e) = self.conn.execute(
                query_insert,
                named_params! {
                    ":new_id": data.creation,
                    ":new_mime": data.mime,
                    ":new_content": data.content,
                    ":new_metadata_mime": data.metadata.as_ref().map(|m| &m.0),
                    ":new_metadata": data.metadata.as_ref().map(|m| &m.1),
                },
            ) {
                if let rusqlite::Error::SqliteFailure(rusqlite::ffi::Error { code, .. }, ..) = e {
                    if code == ErrorCode::ConstraintViolation {
                        warn!("a different value with the same id was already inserted");
                        data.creation += 1;
                        return self.insert(data);
                    }
                }
                return Err(e.into());
            }
        }

        self.hashs.insert(data_hash, data.creation);
        self.state.insert(data.creation, data);

        self.search();
        Ok(())
    }

    pub fn delete(&mut self, data: &Entry) -> Result<()> {
        let query = r#"
            DELETE FROM ClipboardEntries
            WHERE creation = ?1;
        "#;

        self.conn.execute(query, [data.creation])?;

        _ = self.notify_modif();

        self.hashs.remove(&data.get_hash());
        self.state.remove(&data.creation);

        self.search();

        Ok(())
    }

    pub fn clear(&mut self) -> Result<()> {
        let query_delete = r#"
            DELETE FROM ClipboardEntries
        "#;
        self.conn.execute(query_delete, [])?;

        _ = self.notify_modif();

        self.state.clear();
        self.filtered.clear();
        self.hashs.clear();

        Ok(())
    }

    pub fn search(&mut self) {
        if self.query.is_empty() {
            self.filtered.clear();
        } else if let Some(atom) = &self.needle {
            self.filtered = self
                .state
                .iter()
                .rev()
                .filter_map(|(id, data)| {
                    data.get_searchable_text().and_then(|text| {
                        let mut buf = Vec::new();

                        let haystack = Utf32Str::new(text, &mut buf);

                        let mut indices = Vec::new();

                        let _res = atom.indices(haystack, &mut self.matcher, &mut indices);

                        if !indices.is_empty() {
                            Some((*id, indices))
                        } else {
                            None
                        }
                    })
                })
                .collect::<Vec<_>>();
        }
    }

    pub fn set_query_and_search(&mut self, query: String) {
        if query.is_empty() {
            self.needle.take();
        } else {
            let atom = Atom::new(
                &query,
                CaseMatching::Smart,
                Normalization::Smart,
                AtomKind::Substring,
                true,
            );

            self.needle.replace(atom);
        }

        self.query = query;

        self.search();
    }

    pub fn query(&self) -> &str {
        &self.query
    }

    pub fn get(&self, index: usize) -> Option<&Entry> {
        if self.query.is_empty() {
            // because we expose the tree in reverse
            self.state.iter().rev().nth(index).map(|e| e.1)
        } else {
            self.filtered
                .get(index)
                .map(|(id, _indices)| &self.state[id])
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &'_ Entry> {
        debug_assert!(self.query.is_empty());
        self.state.values().rev()
    }

    pub fn search_iter(&self) -> impl Iterator<Item = (&'_ Entry, &'_ Vec<u32>)> {
        debug_assert!(!self.query.is_empty());

        self.filtered
            .iter()
            .map(|(id, indices)| (&self.state[id], indices))
    }

    pub fn len(&self) -> usize {
        if self.query.is_empty() {
            self.state.len()
        } else {
            self.filtered.len()
        }
    }
}

#[derive(Clone, Debug)]
pub enum DbMessage {
    DbWasWritten(u32),
    LockWasRemoved,
}

#[cached]
fn get_base_path() -> PathBuf {
    directories::BaseDirs::new()
        .unwrap()
        .runtime_dir()
        .unwrap()
        .join(APPID)
}

pub fn sub() -> Subscription<AppMessage> {
    subscription::run(|| {
        let (tx, rx) = mpsc::channel();

        let path = directories::BaseDirs::new()
            .unwrap()
            .runtime_dir()
            .unwrap()
            .join(APPID);

        if !path.exists() {
            if let Err(err) = fs::create_dir_all(&path) {
                error!("can't create runtime dir: {}", err);
            }
        }

        let mut e =
            notify::recommended_watcher(move |event_res: Result<notify::Event, notify::Error>| {
                debug!("{:?}", event_res);

                match event_res {
                    Ok(event) => match &event.kind {
                        notify::EventKind::Remove(_) => {
                            if event.paths[0].ends_with(LOCK_FILE) {
                                if let Err(err) =
                                    tx.send(AppMessage::DbMessage(DbMessage::LockWasRemoved))
                                {
                                    warn!("failed to send notify event: {:?}", err);
                                }
                            }
                        }
                        notify::EventKind::Modify(notify::event::ModifyKind::Data(_)) => {
                            if event.paths[0].ends_with(MODIF_FILE) {
                                let Ok(bytes) = fs::read(&event.paths[0]) else {
                                    return;
                                };

                                if bytes.len() == 4 {
                                    let id_bytes: [u8; 4] = bytes[0..4]
                                        .try_into()
                                        .expect("slice with incorrect length");
                                    let id = u32::from_ne_bytes(id_bytes);

                                    if let Err(err) =
                                        tx.send(AppMessage::DbMessage(DbMessage::DbWasWritten(id)))
                                    {
                                        warn!("failed to send notify event: {:?}", err);
                                    }
                                }
                            }
                        }
                        _ => {}
                    },
                    Err(err) => {
                        warn!("failed to watch files: {:?}", err);
                    }
                }
            })
            .unwrap();

        debug!("will watch {}", path.display());

        if let Err(err) = e.watch(&path, notify::RecursiveMode::NonRecursive) {
            warn!("failed to watch file: {:?}", err);
        }

        debug!("we are watching!");

        futures::stream::iter(rx)
    })
}

#[cfg(test)]
mod test {
    use std::{
        fs::{self, File},
        io::{Read, Write},
        path::PathBuf,
        thread::sleep,
        time::Duration,
    };

    use serial_test::serial;

    use anyhow::Result;
    use cosmic::{iced_sctk::util, widget::canvas::Path};

    use crate::{
        config::Config,
        utils::{self, remove_dir_contents},
    };

    use super::{Db, Entry};

    fn prepare_db_dir() -> PathBuf {
        let db_dir = PathBuf::from("tests");
        let _ = std::fs::create_dir_all(&db_dir);
        remove_dir_contents(&db_dir);
        db_dir
    }

    #[test]
    #[serial]
    fn test() -> Result<()> {
        let db_dir = prepare_db_dir();

        let mut db = Db::inner_new(&Config::default(), &db_dir)?;

        test_db(&mut db).unwrap();

        db.clear()?;

        test_db(&mut db).unwrap();

        Ok(())
    }

    fn test_db(db: &mut Db) -> Result<()> {
        assert!(db.len() == 0);

        let data = Entry::new_now("text/plain".into(), "content".as_bytes().into(), None);

        db.insert(data).unwrap();

        assert!(db.len() == 1);

        sleep(Duration::from_millis(1000));

        let data = Entry::new_now("text/plain".into(), "content".as_bytes().into(), None);

        db.insert(data).unwrap();

        assert!(db.len() == 1);

        sleep(Duration::from_millis(1000));

        let data = Entry::new_now("text/plain".into(), "content2".as_bytes().into(), None);

        db.insert(data.clone()).unwrap();

        assert!(db.len() == 2);

        let next = db.iter().next().unwrap();

        assert!(next.creation == data.creation);
        assert!(next.content == data.content);

        Ok(())
    }

    #[test]
    #[serial]
    fn test_delete_old_one() {
        let db_path = prepare_db_dir();

        let mut db = Db::inner_new(&Config::default(), &db_path).unwrap();

        let data = Entry::new_now("text/plain".into(), "content".as_bytes().into(), None);
        db.insert(data).unwrap();

        sleep(Duration::from_millis(100));

        let data = Entry::new_now("text/plain".into(), "content2".as_bytes().into(), None);
        db.insert(data).unwrap();

        assert!(db.len() == 2);

        let db = Db::inner_new(&Config::default(), &db_path).unwrap();

        assert!(db.len() == 2);

        let config = Config {
            maximum_entries_lifetime: Some(Duration::ZERO),
            ..Default::default()
        };
        let db = Db::inner_new(&config, &db_path).unwrap();

        assert!(db.len() == 0);
    }

    #[test]
    #[serial]
    fn same() {
        let db_path = prepare_db_dir();

        let mut db = Db::inner_new(&Config::default(), &db_path).unwrap();

        let now = utils::now_millis();

        let data = Entry::new(now, "text/plain".into(), "content".as_bytes().into(), None);

        db.insert(data).unwrap();

        let data = Entry::new(now, "text/plain".into(), "content".as_bytes().into(), None);

        db.insert(data).unwrap();
        assert!(db.len() == 1);
    }

    #[test]
    #[serial]
    fn different_content_same_time() {
        let db_path = prepare_db_dir();

        let mut db = Db::inner_new(&Config::default(), &db_path).unwrap();

        let now = utils::now_millis();

        let data = Entry::new(now, "text/plain".into(), "content".as_bytes().into(), None);

        db.insert(data).unwrap();

        let data = Entry::new(now, "text/plain".into(), "content2".as_bytes().into(), None);

        db.insert(data).unwrap();
        assert!(db.len() == 2);
    }
}
