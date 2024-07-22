use cosmic::iced::window::Id;

use crate::{
    clipboard::{self, ClipboardMessage},
    config::Config,
    db::{DbMessage, Entry},
    navigation::NavigationMessage,
};

#[derive(Clone, Debug)]
pub enum AppMessage {
    ChangeConfig(Config),
    TogglePopup,
    ToggleQuickSettings,
    ClosePopup,
    Search(String),
    ClipboardEvent(ClipboardMessage),
    RetryConnectingClipboard,
    Copy(Entry),
    Delete(Entry),
    PrivateMode(bool),
    Clear,
    Navigation(NavigationMessage),
    DbMessage(DbMessage),
}
