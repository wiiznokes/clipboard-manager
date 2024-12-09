use std::{borrow::Cow, cmp::min};

use cosmic::{
    iced::{Alignment, Length, Padding},
    iced_widget::scrollable::{Direction, Scrollbar},
    theme::Button,
    widget::{
        self,
        button::{self},
        column, container, context_menu, horizontal_space, image, menu, row, scrollable, text,
        text_input, toggler,
    },
    Element,
};

use crate::{
    app::AppState,
    db::{Content, Entry},
    fl,
    message::{AppMsg, ConfigMsg},
    utils::formatted_value,
};

#[macro_export]
macro_rules! icon {
    ($name:literal) => {{
        let bytes = include_bytes!(concat!("../../res/icons/", $name, "px.svg"));
        cosmic::widget::icon::from_svg_bytes(bytes)
    }};
}

impl AppState {
    pub fn quick_settings_view(&self) -> Element<'_, AppMsg> {
        fn toggle_settings<'a>(
            info: impl Into<Cow<'a, str>> + 'a,
            value: bool,
            f: impl Fn(bool) -> AppMsg + 'a,
        ) -> Element<'a, AppMsg> {
            row()
                .push(text(info))
                .push(horizontal_space())
                .push(toggler(value).on_toggle(f))
                .into()
        }

        column()
            .width(Length::Fill)
            .spacing(20)
            .padding(10)
            .push(toggle_settings(
                fl!("incognito"),
                self.config.private_mode,
                |v| AppMsg::Config(ConfigMsg::PrivateMode(v)),
            ))
            .push(toggle_settings(
                fl!("horizontal_layout"),
                self.config.horizontal,
                |v| AppMsg::Config(ConfigMsg::Horizontal(v)),
            ))
            .push(toggle_settings(
                fl!("unique_session"),
                self.config.unique_session,
                |v| AppMsg::Config(ConfigMsg::UniqueSession(v)),
            ))
            .push(button::destructive(fl!("clear_entries")).on_press(AppMsg::Clear))
            .into()
    }

    pub fn popup_view(&self) -> Element<'_, AppMsg> {
        column()
            .push(self.top_bar())
            .push(self.content())
            .spacing(20)
            .padding(10)
            .align_x(Alignment::Center)
            // .width(Length::Fill)
            // .height(Length::Fill)
            .height(if self.config.horizontal {
                Length::Fill
            } else {
                Length::Fixed(530f32)
            })
            .width(if self.config.horizontal {
                Length::Fill
            } else {
                Length::Fixed(400f32)
            })
            .into()
    }

    fn top_bar(&self) -> Element<'_, AppMsg> {
        let content: Element<_> = match self.qr_code.is_none() {
            true => text_input::search_input(fl!("search_entries"), self.db.query())
                .always_active()
                .on_input(AppMsg::Search)
                .on_paste(AppMsg::Search)
                .on_clear(AppMsg::Search("".into()))
                .width(match self.config.horizontal {
                    true => Length::Fixed(250f32),
                    false => Length::Fill,
                })
                .into(),
            false => button::text(fl!("return_to_clipboard"))
                .on_press(AppMsg::ReturnToClipboard)
                .width(match self.config.horizontal {
                    true => Length::Shrink,
                    false => Length::Fill,
                })
                .into(),
        };

        container(content)
            .padding(Padding::new(10f32).bottom(0))
            .into()
    }

    fn content(&self) -> Element<'_, AppMsg> {
        match &self.qr_code {
            Some(qr_code) => {
                let qr_code_content: Element<_> = match qr_code {
                    Ok(c) => widget::qr_code(c).into(),
                    Err(()) => text(fl!("qr_code_error")).into(),
                };

                return container(qr_code_content).center(Length::Fill).into();
            }
            None => {
                let entries_view: Vec<_> = if self.db.query().is_empty() {
                    self.db
                        .iter()
                        .enumerate()
                        .filter_map(|(pos, data)| match data.get_content() {
                            Ok(c) => match c {
                                Content::Text(text) => {
                                    self.text_entry(data, pos == self.focused, text)
                                }
                                Content::Image(image) => {
                                    self.image_entry(data, pos == self.focused, image)
                                }
                                Content::UriList(uris) => {
                                    self.uris_entry(data, pos == self.focused, &uris)
                                }
                            },
                            Err(_) => None,
                        })
                        .collect()
                } else {
                    self.db
                        .search_iter()
                        .enumerate()
                        .filter_map(|(pos, (data, indices))| match data.get_content() {
                            Ok(c) => match c {
                                Content::Text(text) => self.text_entry_with_indices(
                                    data,
                                    pos == self.focused,
                                    text,
                                    indices,
                                ),
                                Content::Image(image) => {
                                    self.image_entry(data, pos == self.focused, image)
                                }
                                Content::UriList(uris) => {
                                    self.uris_entry(data, pos == self.focused, &uris)
                                }
                            },
                            Err(_) => None,
                        })
                        .collect()
                };

                if self.config.horizontal {
                    // try to fix scroll bar
                    let padding = Padding {
                        top: 0f32,
                        right: 10f32,
                        bottom: 20f32,
                        left: 10f32,
                    };

                    let column = row::with_children(entries_view)
                        .spacing(5f32)
                        .padding(padding);

                    scrollable(column)
                        .direction(Direction::Horizontal(Scrollbar::default()))
                        .into()
                } else {
                    // try to fix scroll bar
                    let padding = Padding {
                        top: 0f32,
                        right: 20f32,
                        bottom: 0f32,
                        left: 10f32,
                    };

                    let column = column::with_children(entries_view)
                        .spacing(5f32)
                        .padding(padding);

                    scrollable(column)
                        // XXX: why ?
                        .height(Length::FillPortion(2))
                        .into()
                }
            }
        }
    }

    fn image_entry<'a>(
        &'a self,
        entry: &'a Entry,
        is_focused: bool,
        image_data: &'a [u8],
    ) -> Option<Element<'a, AppMsg>> {
        let handle = image::Handle::from_bytes(image_data.to_owned());

        Some(self.base_entry(entry, is_focused, image(handle).width(Length::Fill)))
    }

    fn uris_entry<'a>(
        &'a self,
        entry: &'a Entry,
        is_focused: bool,
        uris: &[&'a str],
    ) -> Option<Element<'a, AppMsg>> {
        if uris.is_empty() {
            return None;
        }

        let max = 3;

        let mut lines = Vec::with_capacity(min(uris.len(), max + 1));

        for uri in uris.iter().take(max) {
            lines.push(text(*uri).into());
        }

        if uris.len() > max {
            lines.push(text("...").into());
        }

        Some(self.base_entry(
            entry,
            is_focused,
            column::with_children(lines).width(Length::Fill),
        ))
    }

    fn text_entry_with_indices<'a>(
        &'a self,
        entry: &'a Entry,
        is_focused: bool,
        content: &'a str,
        _indices: &'a [u32],
    ) -> Option<Element<'a, AppMsg>> {
        self.text_entry(entry, is_focused, content)
    }

    fn text_entry<'a>(
        &'a self,
        entry: &'a Entry,
        is_focused: bool,
        content: &'a str,
    ) -> Option<Element<'a, AppMsg>> {
        if content.is_empty() {
            return None;
        }
        // todo: remove this max line things: display the maximum
        if self.config.horizontal {
            Some(self.base_entry(entry, is_focused, text(formatted_value(content, 10, 500))))
        } else {
            Some(self.base_entry(entry, is_focused, text(formatted_value(content, 5, 200))))
        }
    }

    fn base_entry<'a>(
        &'a self,
        entry: &'a Entry,
        is_focused: bool,
        content: impl Into<Element<'a, AppMsg>>,
    ) -> Element<'a, AppMsg> {
        let btn = button::custom(content)
            .on_press(AppMsg::Copy(entry.clone()))
            .padding([8, 16])
            .class(Button::Custom {
                active: Box::new(move |focused, theme| {
                    let rad_s = theme.cosmic().corner_radii.radius_s;
                    let focused = is_focused || focused;

                    let a = if focused {
                        button::Catalog::hovered(theme, focused, focused, &Button::Text)
                    } else {
                        button::Catalog::active(theme, focused, focused, &Button::Standard)
                    };
                    button::Style {
                        border_radius: rad_s.into(),
                        outline_width: 0.0,
                        ..a
                    }
                }),
                hovered: Box::new(move |focused, theme| {
                    let focused = is_focused || focused;
                    let rad_s = theme.cosmic().corner_radii.radius_s;

                    let text = button::Catalog::hovered(theme, focused, focused, &Button::Text);
                    button::Style {
                        border_radius: rad_s.into(),
                        outline_width: 0.0,
                        ..text
                    }
                }),
                disabled: Box::new(|theme| button::Catalog::disabled(theme, &Button::Text)),
                pressed: Box::new(move |focused, theme| {
                    let focused = is_focused || focused;
                    let rad_s = theme.cosmic().corner_radii.radius_s;

                    let text = button::Catalog::pressed(theme, focused, focused, &Button::Text);
                    button::Style {
                        border_radius: rad_s.into(),
                        outline_width: 0.0,
                        ..text
                    }
                }),
            });

        let btn: Element<_> = if self.config.horizontal {
            container(btn.width(Length::Fill).height(Length::Fill))
                .max_width(350f32)
                .into()
        } else {
            btn.width(Length::Fill).into()
        };

        context_menu(
            btn,
            Some(vec![
                menu::Tree::new(
                    button::text(fl!("delete_entry"))
                        .on_press(AppMsg::Delete(entry.clone()))
                        .width(Length::Fill)
                        .class(Button::Destructive),
                ),
                menu::Tree::new(
                    button::text(fl!("show_qr_code"))
                        .on_press(AppMsg::ShowQrCode(entry.clone()))
                        .width(Length::Fill),
                ),
                if entry.is_favorite {
                    menu::Tree::new(
                        button::text(fl!("remove_favorite"))
                            .on_press(AppMsg::RemoveFavorite(entry.clone()))
                            .width(Length::Fill),
                    )
                } else {
                    menu::Tree::new(
                        button::text(fl!("add_favorite"))
                            .on_press(AppMsg::AddFavorite(entry.clone()))
                            .width(Length::Fill),
                    )
                },
            ]),
        )
        .into()
    }
}
