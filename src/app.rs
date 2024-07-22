use cosmic::app::{command, Core};

use cosmic::cctk::sctk::reexports::protocols::wp::presentation_time::client::wp_presentation_feedback::Kind;
use cosmic::iced::advanced::subscription;
use cosmic::iced::wayland::popup::{destroy_popup, get_popup};
use cosmic::iced::window::Id;
use cosmic::iced::{self, event, Command, Limits};

use cosmic::iced_futures::Subscription;
use cosmic::iced_runtime::command::Action;
use cosmic::iced_runtime::core::window;
use cosmic::iced_style::application;
use cosmic::iced_widget::graphics::text::cosmic_text::rustybuzz::ttf_parser::name_id::POST_SCRIPT_NAME;
use cosmic::iced_widget::Column;
use cosmic::widget::{button, icon, text, text_input, MouseArea};

use cosmic::{Element, Theme};

use crate::config::{Config, CONFIG_VERSION, PRIVATE_MODE};
use crate::db::{self, Db, Entry};
use crate::message::AppMessage;
use crate::utils::command_message;
use crate::view::{popup_view, quick_settings_view};
use crate::{clipboard, config, navigation};

use cosmic::cosmic_config;
use std::sync::atomic::{self, AtomicBool};

pub const QUALIFIER: &str = "io.github";
pub const ORG: &str = "wiiznokes";
pub const APP: &str = "cosmic-ext-applet-clipboard-manager";
pub const APPID: &str = constcat::concat!(QUALIFIER, ".", ORG, ".", APP);

pub struct Window {
    core: Core,
    config: Config,
    config_handler: cosmic_config::Config,
    popup: Option<Popup>,
    state: AppState,
}

pub struct AppState {
    pub db: Db,
    pub clipboard_state: ClipboardState,
    pub focused: usize,
    pub id: u32,
}

impl AppState {
    fn focus_next(&mut self) {
        self.focused = (self.focused + 1) % self.db.len();
    }

    fn focus_previous(&mut self) {
        self.focused = (self.focused + self.db.len() - 1) % self.db.len();
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClipboardState {
    Init,
    Connected,
    Error(String),
}

impl ClipboardState {
    pub fn is_error(&self) -> bool {
        matches!(self, ClipboardState::Error(..))
    }
}

#[derive(Clone, Debug)]
pub struct Flags {
    pub config_handler: cosmic_config::Config,
    pub config: Config,
}

#[derive(Debug, Clone)]
struct Popup {
    pub kind: PopupKind,
    pub id: window::Id,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum PopupKind {
    Popup,
    QuickSettings,
}

impl Window {
    fn close_popup(&mut self) -> Command<cosmic::app::Message<AppMessage>> {
        self.state.focused = 0;
        self.state.db.set_query_and_search("".into());

        if let Some(popup) = self.popup.take() {
            //info!("destroy {:?}", popup.id);
            destroy_popup(popup.id)
        } else {
            Command::none()
        }
    }

    fn toogle_popup(&mut self, kind: PopupKind) -> Command<cosmic::app::Message<AppMessage>> {
        match &self.popup {
            Some(popup) => {
                if popup.kind == kind {
                    self.close_popup()
                } else {
                    Command::batch(vec![self.close_popup(), self.open_popup(kind)])
                }
            }
            None => self.open_popup(kind),
        }
    }

    fn open_popup(&mut self, kind: PopupKind) -> Command<cosmic::app::Message<AppMessage>> {
        let new_id = Id::unique();
        //info!("will create {:?}", new_id);

        let popup = Popup { kind, id: new_id };

        self.popup.replace(popup);
        let mut popup_settings =
            self.core
                .applet
                .get_popup_settings(Id::MAIN, new_id, None, None, None);

        match kind {
            PopupKind::Popup => {
                popup_settings.positioner.size_limits = Limits::NONE
                    .max_width(400.0)
                    .min_width(300.0)
                    .min_height(200.0)
                    .max_height(500.0);
                get_popup(popup_settings)
            }
            PopupKind::QuickSettings => {
                popup_settings.positioner.size_limits = Limits::NONE
                    .max_width(250.0)
                    .min_width(200.0)
                    .min_height(200.0)
                    .max_height(550.0);

                get_popup(popup_settings)
            }
        }
    }
}

impl cosmic::Application for Window {
    type Executor = cosmic::executor::Default;
    type Flags = Flags;
    type Message = AppMessage;
    const APP_ID: &'static str = APPID;

    fn core(&self) -> &Core {
        &self.core
    }

    fn core_mut(&mut self) -> &mut Core {
        &mut self.core
    }

    fn init(
        core: Core,
        flags: Self::Flags,
    ) -> (Self, cosmic::Command<cosmic::app::Message<Self::Message>>) {
        let config = flags.config;
        PRIVATE_MODE.store(config.private_mode, atomic::Ordering::Relaxed);
        let window = Window {
            core,
            config_handler: flags.config_handler,
            popup: None,
            state: AppState {
                db: db::Db::new(&config).unwrap(),
                clipboard_state: ClipboardState::Init,
                focused: 0,
                id: rand::random(),
            },
            config,
        };

        
        debug!("{:?}", window.state.db);

        #[cfg(debug_assertions)]
        let command = Command::single(Action::Future(Box::pin(async {
            cosmic::app::Message::App(AppMessage::TogglePopup)
        })));

        #[cfg(not(debug_assertions))]
        let command = Command::none();

        (window, command)
    }

    fn on_close_requested(&self, id: window::Id) -> Option<AppMessage> {
        info!("on_close_requested");

        if let Some(popup) = &self.popup {
            if popup.id == id {
                return Some(AppMessage::ClosePopup);
            }
        }
        None
    }

    fn update(&mut self, message: Self::Message) -> Command<cosmic::app::Message<Self::Message>> {
        macro_rules! config_set {
            ($name: ident, $value: expr) => {
                match paste::paste! { self.config.[<set_ $name>](&self.config_handler, $value) } {
                    Ok(_) => {}
                    Err(err) => {
                        error!("failed to save config {:?}: {}", stringify!($name), err);
                    }
                }
            };
        }

        match message {
            AppMessage::ChangeConfig(config) => {
                if config != self.config {
                    PRIVATE_MODE.store(config.private_mode, atomic::Ordering::Relaxed);
                    self.config = config;
                }
            }
            AppMessage::ToggleQuickSettings => {
                return self.toogle_popup(PopupKind::QuickSettings);
            }

            AppMessage::TogglePopup => {
                return self.toogle_popup(PopupKind::Popup);
            }
            AppMessage::ClosePopup => return self.close_popup(),
            AppMessage::Search(query) => {
                self.state.db.set_query_and_search(query);
            }
            AppMessage::ClipboardEvent(message) => match message {
                clipboard::ClipboardMessage::Connected => {
                    self.state.clipboard_state = ClipboardState::Connected;
                }
                clipboard::ClipboardMessage::Data(data) => {
                    if let Err(e) = self.state.db.insert(data) {
                        error!("can't insert data: {e}");
                    }
                }
                clipboard::ClipboardMessage::Error(e) => {
                    error!("{e}");
                    self.state.clipboard_state = ClipboardState::Error(e);
                }
                clipboard::ClipboardMessage::EmptyKeyboard => {
                    if let Some(data) = self.state.db.get(0) {
                        if let Err(e) = clipboard::copy(data.to_owned()) {
                            error!("can't copy: {e}");
                        }
                    }
                }
            },
            AppMessage::Copy(data) => {
                if let Err(e) = clipboard::copy(data) {
                    error!("can't copy: {e}");
                }
                return self.close_popup();
            }
            AppMessage::Delete(data) => {
                if let Err(e) = self.state.db.delete(&data) {
                    error!("can't delete {:?}: {}", data.get_content(), e);
                }
            }
            AppMessage::Clear => {
                if let Err(e) = self.state.db.clear() {
                    error!("can't clear db: {e}");
                }
            }
            AppMessage::RetryConnectingClipboard => {
                self.state.clipboard_state = ClipboardState::Init;
            }
            AppMessage::Navigation(message) => match message {
                navigation::NavigationMessage::Next => {
                    self.state.focus_next();
                }
                navigation::NavigationMessage::Previous => {
                    self.state.focus_previous();
                }
                navigation::NavigationMessage::Enter => {
                    if let Some(data) = self.state.db.get(self.state.focused) {
                        if let Err(e) = clipboard::copy(data.clone()) {
                            error!("can't copy: {e}");
                        }
                        return self.close_popup();
                    }
                }
                navigation::NavigationMessage::Quit => {
                    return self.close_popup();
                }
            },
            AppMessage::PrivateMode(private_mode) => {
                config_set!(private_mode, private_mode);
                PRIVATE_MODE.store(private_mode, atomic::Ordering::Relaxed);
            }
            AppMessage::DbMessage(inner) => {
                if let Err(err) = self.state.db.update(inner) {
                    error!("{}", err);
                }
            }
        }
        Command::none()
    }

    fn view(&self) -> Element<Self::Message> {
        let icon = self
            .core
            .applet
            .icon_button(constcat::concat!(APPID, "-symbolic"))
            .on_press(AppMessage::TogglePopup);

        MouseArea::new(icon)
            .on_right_release(AppMessage::ToggleQuickSettings)
            .into()
    }

    fn view_window(&self, _id: Id) -> Element<Self::Message> {
        let Some(popup) = &self.popup else {
            return self
                .core
                .applet
                .popup_container(popup_view(&self.state, &self.config))
                .into();
        };

        let view = match &popup.kind {
            PopupKind::Popup => popup_view(&self.state, &self.config),
            PopupKind::QuickSettings => quick_settings_view(&self.state, &self.config),
        };

        self.core.applet.popup_container(view).into()
    }
    fn subscription(&self) -> Subscription<Self::Message> {
        let mut subscriptions = vec![
            config::sub(),
            navigation::sub().map(AppMessage::Navigation),
            db::sub(),
        ];

        if !self.state.clipboard_state.is_error() {
            subscriptions.push(clipboard::sub().map(AppMessage::ClipboardEvent));
        }

        Subscription::batch(subscriptions)
    }

    fn style(&self) -> Option<<Theme as application::StyleSheet>::Style> {
        Some(cosmic::applet::style())
    }
}
