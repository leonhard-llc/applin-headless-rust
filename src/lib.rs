//! # `applin_headless`
//!
//! [![crates.io version](https://img.shields.io/crates/v/applin_headless.svg)](https://crates.io/crates/applin_headless)
//! [![unsafe forbidden](https://raw.githubusercontent.com/leonhard-llc/applin-headless-rust/main/unsafe-forbidden-success.svg)](https://github.com/rust-secure-code/safety-dance/)
//! [![pipeline status](https://github.com/leonhard-llc/applin-headless-rust/workflows/CI/badge.svg)](https://github.com/leonhard-llc/applin-headless-rust/actions)
//!
//! Create an Applin™ client and control it from Rust code. Great for tests.
//!
//! <https://www.applin.dev/>
//!
//! # Cargo Geiger Safety Report
//!
//! # Changelog
//!
//! - v0.3.1 - Lint.
//! - v0.3.0 2024-11-17
//!     - Change signature of [`ApplinClient::is_checked`] to take `&Widget`.
//!     - Rename `WidgetExtension::vars` to [`WidgetExtension::var_names_and_initials`].
//! - v0.2.0 2024-11-13
//!     - Add `cookie_file_path` arg to `ApplinClient::new`.
//!     - Add `log_pages`.
//! - v0.1.1 2024-11-03 - Add `is_checked`.
//! - v0.1.0 - Impersonates applin-ios 0.38.0.
#![forbid(unsafe_code)]

use applin::action::{pop, Action};
use applin::page::{Page, PlainPage};
use applin::util::Real32;
use applin::widget::{empty, Column, Form, FormSection, GroupedRowTable, Scroll, Widget};
use applin::ApplinResponse;
use cookie_store::{CookieExpiration, CookieStore};
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::io::{BufReader, BufWriter, ErrorKind, Write};
use std::path::PathBuf;
use std::time::Duration;
use ureq::serde_json::{Number, Value};
use url::Url;

#[allow(clippy::needless_lifetimes)]
pub trait WidgetExtension {
    /// # Errors
    /// Returns `Err` when called on a widget type that cannot have actions.
    fn actions(&self) -> Result<&Vec<Action>, String>;
    #[must_use]
    fn clone_shallow(&self) -> Self;
    fn depth_first_walk<'x>(&'x self, f: &mut impl FnMut(&'x Widget));
    #[must_use]
    fn descendents(&self) -> Vec<&Widget>;
    #[must_use]
    fn error(&self) -> &str;
    #[must_use]
    fn id(&self) -> &str;
    #[must_use]
    fn subs(&self) -> Vec<&Widget>;
    #[must_use]
    fn text(&self) -> &str;
    #[must_use]
    fn validated(&self) -> bool;
    /// Gets the widget's variable names and initial values.
    fn var_names_and_initials(&self) -> Vec<(&str, Var)>;
}

impl WidgetExtension for Widget {
    fn actions(&self) -> Result<&Vec<Action>, String> {
        match self {
            Widget::Column(..)
            | Widget::Empty(..)
            | Widget::ErrorText(..)
            | Widget::Form(..)
            | Widget::FormSection(..)
            | Widget::GroupedRowTable(..)
            | Widget::Image(..)
            | Widget::LastErrorText(..)
            | Widget::Scroll(..)
            | Widget::Selector(..)
            | Widget::Text(..)
            | Widget::Textfield(..) => Err(format!("widget has no actions: {self:?}")),
            Widget::BackButton(inner) => Ok(&inner.actions),
            Widget::Button(inner) => Ok(&inner.actions),
            Widget::Checkbox(inner) => Ok(&inner.actions),
            Widget::CheckboxButton(inner) => Ok(&inner.actions),
            Widget::FormButton(inner) => Ok(&inner.actions),
            Widget::NavButton(inner) => Ok(&inner.actions),
        }
    }

    fn clone_shallow(&self) -> Self {
        match self {
            Widget::BackButton(..)
            | Widget::Button(..)
            | Widget::Checkbox(..)
            | Widget::CheckboxButton(..)
            | Widget::Empty(..)
            | Widget::ErrorText(..)
            | Widget::FormButton(..)
            | Widget::Image(..)
            | Widget::LastErrorText(..)
            | Widget::NavButton(..)
            | Widget::Selector(..)
            | Widget::Text(..)
            | Widget::Textfield(..) => self.clone(),
            Widget::Column(inner) => Widget::Column(Column {
                align: inner.align,
                id: inner.id.clone(),
                spacing: inner.spacing,
                widgets: vec![],
            }),
            Widget::Form(inner) => Widget::Form(Form {
                id: inner.id.clone(),
                widgets: vec![],
            }),
            Widget::FormSection(inner) => Widget::FormSection(FormSection {
                id: inner.id.clone(),
                title: inner.title.clone(),
                widgets: vec![],
            }),
            Widget::GroupedRowTable(inner) => Widget::GroupedRowTable(GroupedRowTable {
                id: inner.id.clone(),
                row_groups: vec![],
                spacing: inner.spacing,
            }),
            Widget::Scroll(inner) => Widget::Scroll(Scroll {
                id: inner.id.clone(),
                widget: Box::new(empty().into()),
            }),
        }
    }

    fn depth_first_walk<'x>(&'x self, f: &mut impl FnMut(&'x Widget)) {
        f(self);
        match self {
            Widget::BackButton(..)
            | Widget::Button(..)
            | Widget::Checkbox(..)
            | Widget::CheckboxButton(..)
            | Widget::Empty(..)
            | Widget::ErrorText(..)
            | Widget::FormButton(..)
            | Widget::Image(..)
            | Widget::LastErrorText(..)
            | Widget::NavButton(..)
            | Widget::Selector(..)
            | Widget::Text(..)
            | Widget::Textfield(..) => {}
            Widget::Column(inner) => inner
                .widgets
                .iter()
                .for_each(|widget: &'x Widget| widget.depth_first_walk(f)),
            Widget::Form(inner) => inner
                .widgets
                .iter()
                .for_each(|widget| widget.depth_first_walk(f)),
            Widget::FormSection(inner) => inner
                .widgets
                .iter()
                .for_each(|widget| widget.depth_first_walk(f)),
            Widget::GroupedRowTable(inner) => inner.row_groups.iter().for_each(|group| {
                group
                    .0
                    .iter()
                    .flatten()
                    .flatten()
                    .for_each(|widget| widget.depth_first_walk(f));
            }),
            Widget::Scroll(inner) => inner.widget.depth_first_walk(f),
        }
    }

    fn descendents<'x>(&'x self) -> Vec<&'x Widget> {
        let mut result: Vec<&'x Widget> = vec![];
        self.depth_first_walk(&mut |widget: &'x Widget| result.push(widget));
        result
    }

    fn error(&self) -> &str {
        match self {
            Widget::BackButton(..)
            | Widget::Button(..)
            | Widget::Checkbox(..)
            | Widget::CheckboxButton(..)
            | Widget::Column(..)
            | Widget::Empty(..)
            | Widget::ErrorText(..)
            | Widget::Form(..)
            | Widget::FormButton(..)
            | Widget::FormSection(..)
            | Widget::GroupedRowTable(..)
            | Widget::Image(..)
            | Widget::LastErrorText(..)
            | Widget::NavButton(..)
            | Widget::Scroll(..)
            | Widget::Text(..) => "",
            Widget::Selector(inner) => inner.error.as_str(),
            Widget::Textfield(inner) => inner.error.as_str(),
        }
    }

    fn id(&self) -> &str {
        match self {
            Widget::BackButton(inner) => inner.id.as_str(),
            Widget::Button(inner) => inner.id.as_str(),
            Widget::Checkbox(inner) => inner.id.as_str(),
            Widget::CheckboxButton(inner) => inner.id.as_str(),
            Widget::Column(inner) => inner.id.as_str(),
            Widget::Empty(inner) => inner.id.as_str(),
            Widget::ErrorText(inner) => inner.id.as_str(),
            Widget::Form(inner) => inner.id.as_str(),
            Widget::FormButton(inner) => inner.id.as_str(),
            Widget::FormSection(inner) => inner.id.as_str(),
            Widget::GroupedRowTable(inner) => inner.id.as_str(),
            Widget::Image(inner) => inner.id.as_str(),
            Widget::LastErrorText(inner) => inner.id.as_str(),
            Widget::NavButton(inner) => inner.id.as_str(),
            Widget::Scroll(inner) => inner.id.as_str(),
            Widget::Selector(inner) => inner.id.as_str(),
            Widget::Text(inner) => inner.id.as_str(),
            Widget::Textfield(inner) => inner.id.as_str(),
        }
    }

    fn subs(&self) -> Vec<&Widget> {
        match self {
            Widget::BackButton(..)
            | Widget::Button(..)
            | Widget::Checkbox(..)
            | Widget::CheckboxButton(..)
            | Widget::Empty(..)
            | Widget::ErrorText(..)
            | Widget::FormButton(..)
            | Widget::Image(..)
            | Widget::LastErrorText(..)
            | Widget::NavButton(..)
            | Widget::Selector(..)
            | Widget::Text(..)
            | Widget::Textfield(..) => vec![],
            Widget::Column(inner) => inner.widgets.iter().collect(),
            Widget::Form(inner) => inner.widgets.iter().collect(),
            Widget::FormSection(inner) => inner.widgets.iter().collect(),
            Widget::GroupedRowTable(inner) => {
                let mut result = vec![];
                for group in &inner.row_groups {
                    for widget in group.0.iter().flatten().flatten() {
                        result.push(widget);
                    }
                }
                result
            }
            Widget::Scroll(inner) => vec![&inner.widget],
        }
    }

    fn text(&self) -> &str {
        match self {
            Widget::BackButton(..)
            | Widget::Column(..)
            | Widget::Empty(..)
            | Widget::Form(..)
            | Widget::GroupedRowTable(..)
            | Widget::Image(..)
            | Widget::LastErrorText(..)
            | Widget::Scroll(..)
            | Widget::Textfield(..) => "",
            Widget::Button(inner) => inner.text.as_str(),
            Widget::Checkbox(inner) => inner.text.as_str(),
            Widget::CheckboxButton(inner) => inner.text.as_str(),
            Widget::ErrorText(inner) => inner.text.as_str(),
            Widget::FormButton(inner) => inner.text.as_str(),
            Widget::FormSection(inner) => inner.title.as_str(),
            Widget::NavButton(inner) => inner.text.as_str(),
            Widget::Selector(inner) => inner.label.as_str(),
            Widget::Text(inner) => inner.text.as_str(),
        }
    }

    fn validated(&self) -> bool {
        match self {
            Widget::BackButton(..)
            | Widget::Button(..)
            | Widget::CheckboxButton(..)
            | Widget::Column(..)
            | Widget::Empty(..)
            | Widget::ErrorText(..)
            | Widget::Form(..)
            | Widget::FormButton(..)
            | Widget::FormSection(..)
            | Widget::GroupedRowTable(..)
            | Widget::Image(..)
            | Widget::LastErrorText(..)
            | Widget::NavButton(..)
            | Widget::Scroll(..)
            | Widget::Text(..) => false,
            Widget::Checkbox(inner) => inner.validated,
            Widget::Selector(inner) => inner.validated,
            Widget::Textfield(inner) => inner.validated,
        }
    }

    #[allow(clippy::needless_lifetimes)]
    fn var_names_and_initials<'x>(&'x self) -> Vec<(&'x str, Var)> {
        match self {
            Widget::BackButton(..)
            | Widget::Button(..)
            | Widget::CheckboxButton(..)
            | Widget::Column(..)
            | Widget::Empty(..)
            | Widget::ErrorText(..)
            | Widget::Form(..)
            | Widget::FormButton(..)
            | Widget::FormSection(..)
            | Widget::GroupedRowTable(..)
            | Widget::Image(..)
            | Widget::LastErrorText(..)
            | Widget::NavButton(..)
            | Widget::Scroll(..)
            | Widget::Text(..) => vec![],
            Widget::Checkbox(inner) => {
                vec![(inner.var_name.as_str(), Var::Bool(inner.initial_bool))]
            }
            Widget::Selector(inner) => {
                let mut result = vec![(
                    inner.var_name.as_str(),
                    Var::String(inner.initial_string.clone()),
                )];
                if !inner.var_name1.is_empty() {
                    result.push((
                        inner.var_name1.as_str(),
                        Var::String(inner.initial_string1.clone()),
                    ));
                }
                if !inner.var_name2.is_empty() {
                    result.push((
                        inner.var_name2.as_str(),
                        Var::String(inner.initial_string2.clone()),
                    ));
                }
                result
            }
            Widget::Textfield(inner) => {
                vec![(
                    inner.var_name.as_str(),
                    Var::String(inner.initial_string.clone()),
                )]
            }
        }
    }
}

pub trait PageExtension {
    #[must_use]
    fn descendents(&self) -> Vec<&Widget>;
    #[must_use]
    fn id(&self) -> &str;
    #[must_use]
    fn subs(&self) -> Vec<&Widget>;
    #[must_use]
    fn title(&self) -> &str;
    #[must_use]
    fn vars(&self) -> Vec<(&str, Var)>;
}

impl PageExtension for Page {
    fn descendents(&self) -> Vec<&Widget> {
        match self {
            Page::Nav(page) => page.widget.descendents(),
            Page::Plain(page) => page.widget.descendents(),
        }
    }

    fn id(&self) -> &str {
        match self {
            Page::Nav(page) => &page.id,
            Page::Plain(page) => &page.id,
        }
    }

    fn subs(&self) -> Vec<&Widget> {
        match self {
            Page::Nav(page) => page.widget.subs(),
            Page::Plain(page) => page.widget.subs(),
        }
    }

    fn title(&self) -> &str {
        match self {
            Page::Nav(page) => &page.title,
            Page::Plain(page) => &page.title,
        }
    }

    fn vars(&self) -> Vec<(&str, Var)> {
        let widget = match self {
            Page::Nav(inner) => &inner.widget,
            Page::Plain(inner) => &inner.widget,
        };
        let mut result = vec![];
        widget.depth_first_walk(&mut |widget| result.append(&mut widget.var_names_and_initials()));
        result
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Var {
    Bool(bool),
    Number(Real32),
    String(String),
}

impl Var {
    /// # Errors
    /// Returns `Err` when the variable is not boolean.
    pub fn bool(&self) -> Result<bool, String> {
        match self {
            Var::Bool(b) => Ok(*b),
            Var::Number(n) => Err(format!("expected bool var but found number: {n:?}")),
            Var::String(s) => Err(format!("expected bool var but found string: {s}")),
        }
    }

    /// # Errors
    /// Returns `Err` when the variable is not a number.
    pub fn number(&self) -> Result<Real32, String> {
        match self {
            Var::Bool(b) => Err(format!("expected number var but found bool: {b}")),
            Var::Number(n) => Ok(*n),
            Var::String(s) => Err(format!("expected number var but found string: {s}")),
        }
    }

    /// # Errors
    /// Returns `Err` when the variable is not a string.
    pub fn string(&self) -> Result<String, String> {
        match self {
            Var::Bool(b) => Err(format!("expected string var but found bool: {b}")),
            Var::Number(n) => Err(format!("expected string var but found number: {n:?}")),
            Var::String(s) => Ok(s.clone()),
        }
    }
}

impl From<Var> for Value {
    fn from(value: Var) -> Self {
        match value {
            Var::Bool(b) => Value::Bool(b),
            Var::Number(n) => Value::Number(Number::from_f64(f64::from(n.get())).unwrap()),
            Var::String(s) => Value::String(s),
        }
    }
}

impl From<&Var> for Value {
    fn from(value: &Var) -> Self {
        match value {
            Var::Bool(b) => Value::Bool(*b),
            Var::Number(n) => Value::Number(Number::from_f64(f64::from(n.get())).unwrap()),
            Var::String(s) => Value::String(s.clone()),
        }
    }
}

pub struct ApplinClient {
    pub agent: ureq::Agent,
    pub cookies_hash: u64,
    pub cookie_file_path: Option<PathBuf>,
    pub last_error: Option<String>,
    /// Every time we get a new version of a page, print it to stdout.
    pub log_pages: bool,
    pub modal: Option<Action>,
    pub next_photo_upload: Option<Vec<u8>>,
    pub stack: Vec<(String, Page)>,
    pub url: Url,
    pub vars: HashMap<String, Var>,
}

impl ApplinClient {
    /// When `cookie_file_path` is `Some`, the client reads the specified file and writes it
    /// whenever its cookies change.
    /// # Panics
    /// Panics when it fails to parse `url`.
    pub fn new(url: impl AsRef<str>, cookie_file_path: Option<PathBuf>) -> Self {
        let mut agent_builder = ureq::AgentBuilder::new()
            .max_idle_connections(1)
            .timeout(Duration::from_secs(10))
            .redirects(0);
        if let Some(path) = &cookie_file_path {
            match File::open(path) {
                Ok(file) => {
                    let store: CookieStore =
                        cookie_store::serde::json::load(BufReader::new(file)).unwrap();
                    agent_builder = agent_builder.cookie_store(store);
                }
                Err(e) if e.kind() == ErrorKind::NotFound => {}
                Err(e) if e.kind() == ErrorKind::Other && e.raw_os_error() == Some(2) => {}
                Err(e) => panic!("error reading {path:?}: {e}"),
            }
        }
        Self {
            agent: agent_builder.build(),
            cookies_hash: 0,
            cookie_file_path,
            last_error: None,
            log_pages: true,
            modal: None,
            next_photo_upload: None,
            stack: vec![],
            url: Url::parse(url.as_ref()).unwrap(),
            vars: HashMap::new(),
        }
    }

    /// # Errors
    /// Returns `Err` when a modal is visible.
    pub fn back(&mut self) -> Result<bool, String> {
        if self.modal.is_some() {
            return Err("modal is visible, cannot press back".to_string());
        }
        let actions = if let Page::Nav(nav_page) = self.page() {
            if let Some(Widget::BackButton(b)) = &nav_page.start {
                b.actions.clone()
            } else {
                vec![pop()]
            }
        } else {
            vec![pop()]
        };
        self.do_actions(actions)
    }

    /// # Errors
    /// Returns `Err` when the server returns a response other than 2xx or 4xx.
    pub fn process_result(
        &mut self,
        result: Result<ureq::Response, ureq::Error>,
    ) -> Result<Option<ureq::Response>, String> {
        if let Some(path) = &self.cookie_file_path {
            let mut hasher = DefaultHasher::new();
            for cookie in self.agent.cookie_store().iter_unexpired() {
                cookie.domain.hash(&mut hasher);
                cookie.path.hash(&mut hasher);
                match cookie.expires {
                    CookieExpiration::AtUtc(t) => t.hash(&mut hasher),
                    CookieExpiration::SessionEnd => {}
                };
            }
            let new_hash = hasher.finish();
            if self.cookies_hash != new_hash {
                self.cookies_hash = new_hash;
                let file =
                    File::create(path).map_err(|e| format!("error writing {path:?}: {e}"))?;
                let mut writer = BufWriter::new(file);
                cookie_store::serde::json::save(&self.agent.cookie_store(), &mut writer)
                    .map_err(|e| e.to_string())?;
                writer.flush().map_err(|e| e.to_string())?;
                println!("wrote {path:?}");
            }
        }
        let response = match result {
            Ok(r) => r,
            Err(ureq::Error::Status(_status, response)) => response,
            Err(ureq::Error::Transport(e)) => return Err(e.to_string()),
        };
        let status_text = response.status_text().to_string();
        let content_type = response.content_type().to_string();
        match response.status() {
            status if (200..=299).contains(&status) => {
                println!("{status} {status_text} content_type={content_type:?}");
            }
            status if (400..=499).contains(&status) => {
                let body = response.into_string().map_err(|e| e.to_string())?;
                println!("{status} {status_text} content_type={content_type:?} body={body:?}");
                self.last_error = Some(body);
                return Ok(None);
            }
            status => return Err(format!("server returned status {status}")),
        }
        Ok(Some(response))
    }

    /// # Errors
    /// Returns `Err` when a request to the server fails.
    /// # Panics
    /// Panics when processing a `pop` action and the stack is empty.
    pub fn do_actions(&mut self, actions: Vec<Action>) -> Result<bool, String> {
        for action in actions {
            let success = match action.typ.as_str() {
                "choose_photo" | "take_photo" => {
                    if let Some(bytes) = self.next_photo_upload.take() {
                        self.upload(&action.url, bytes)?
                    } else {
                        false
                    }
                }
                "modal" => {
                    self.modal = Some(action);
                    true
                }
                "poll" => self.poll()?,
                "pop" => {
                    self.stack.pop();
                    assert!(!self.stack.is_empty());
                    true
                }
                "push" => self.push(&action.page)?,
                "replace_all" => {
                    self.stack.clear();
                    self.push(&action.page)?
                }
                "rpc" => {
                    // TODO: Implement on_user_error_poll.
                    self.rpc(&action.url)?
                }
                "stop_actions" => false,
                _ => true,
            };
            if !success {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// # Errors
    /// Returns `Err` when:
    /// - the widget is not a Checkbox or `CheckboxButton`
    /// - the variable is set and it's not bool
    pub fn is_checked(&self, widget: &Widget) -> Result<bool, String> {
        match widget {
            Widget::Checkbox(inner) => self
                .vars
                .get(&inner.var_name)
                .unwrap_or(&Var::Bool(inner.initial_bool))
                .bool(),
            Widget::CheckboxButton(inner) => Ok(inner.initial_bool),
            _ => Err(format!(
                "widget is not a Checkbox or CheckboxButton: {widget:?}"
            )),
        }
    }

    /// # Errors
    /// Returns `Err` when the widget is not found.
    pub fn find_id(&self, id: impl AsRef<str>) -> Result<&Widget, String> {
        let id = id.as_ref();
        self.page()
            .descendents()
            .into_iter()
            .find(|w| w.id() == id)
            .ok_or_else(|| format!("widget not found with id {id:?}"))
    }

    /// # Errors
    /// Returns `Err` when the widget is not found.
    pub fn find_text(&self, text: impl AsRef<str>) -> Result<&Widget, String> {
        let text = text.as_ref();
        self.page()
            .descendents()
            .into_iter()
            .find(|w| w.text().contains(text))
            .ok_or_else(|| format!("widget not found with text {text:?}"))
    }

    /// # Errors
    /// Returns `Err` when the widget is not found.
    pub fn find_var(&self, var_name: impl AsRef<str>) -> Result<&Widget, String> {
        let var_name = var_name.as_ref();
        self.page()
            .descendents()
            .into_iter()
            .find(|w| {
                w.var_names_and_initials()
                    .iter()
                    .any(|(n, _v)| *n == var_name)
            })
            .ok_or_else(|| format!("widget not found with var_name {var_name:?}"))
    }

    /// # Panics
    /// * Panics when the page stack is empty.
    #[must_use]
    pub fn key(&self) -> &str {
        self.stack.last().unwrap().0.as_str()
    }

    #[must_use]
    pub fn modal(&self) -> Option<&Action> {
        self.modal.as_ref()
    }

    /// # Panics
    /// * Panics when the page stack is empty.
    #[must_use]
    pub fn page(&self) -> &Page {
        &self.stack.last().unwrap().1
    }

    /// # Errors
    /// Returns `Err` when a request to the server fails.
    /// # Panics
    /// * Panics when the page stack is empty.
    pub fn poll(&mut self) -> Result<bool, String> {
        let vars = self.vars();
        let key = self.stack.last().unwrap().0.as_str();
        let url = self.url.join(key).unwrap();
        let (request, opt_body) = if vars.is_empty() {
            println!("GET {url}");
            (self.agent.request_url("GET", &url), None)
        } else {
            let body = self.vars_json_body()?;
            println!("POST {url} {body:?}");
            (self.agent.request_url("POST", &url), Some(body))
        };
        let result = if let Some(body) = opt_body {
            request.send_json(body)
        } else {
            request.call()
        };
        let Some(response) = self.process_result(result)? else {
            return Ok(false);
        };
        assert_eq!(response.content_type(), "application/vnd.applin_response");
        let applin_response: ApplinResponse = response.into_json().map_err(|e| e.to_string())?;
        if self.log_pages {
            println!("{applin_response:?}");
        }
        let mut found_ids = HashSet::new();
        let mut found_var_names = HashSet::new();
        for widget in applin_response.page.descendents() {
            let id = widget.id();
            if !id.is_empty() && !found_ids.insert(id) {
                return Err(format!("page has more than one widget with id {id:?}"));
            }
            for (var_name, _var) in widget.var_names_and_initials() {
                if !found_var_names.insert(var_name) {
                    return Err(format!(
                        "page has more than one widget with var_name {var_name:?}"
                    ));
                }
            }
        }
        self.stack.last_mut().unwrap().1 = applin_response.page;
        Ok(true)
    }

    /// # Errors
    /// * Returns `Err` when the page is already on the stack.
    /// * Returns `Err` when the request to the server fails.
    /// * Returns `Err` when the server returns a response other than 2xx or 4xx.
    pub fn push(&mut self, key: impl AsRef<str>) -> Result<bool, String> {
        let key = key.as_ref();
        if self.stack.iter().any(|(k, _p)| k == key) {
            return Err(format!(
                "cannot push page {key:?} because it is already on the stack"
            ));
        }
        self.stack
            .push((key.to_string(), Page::Plain(PlainPage::new("", empty()))));
        let success = self.poll()?;
        if success && self.page().descendents().iter().any(|w| w.validated()) {
            return self.poll();
        }
        Ok(success)
    }

    /// # Errors
    /// * Returns `Err` when the page contains multiple widgets with the same name.
    pub fn vars_json_body(&self) -> Result<HashMap<String, Value>, String> {
        let mut body: HashMap<String, Value> = HashMap::new();
        let vars = self.vars();
        for (name, var) in &vars {
            if let Some((array_name, array_value)) = name.split_once('%') {
                let json_value = Value::String(array_value.to_string());
                match body.get_mut(array_name) {
                    None => {
                        body.insert(array_name.to_string(), Value::Array(vec![json_value]));
                    }
                    Some(Value::Array(ref mut array)) => array.push(json_value),
                    Some(_) => {
                        return Err(format!(
                            "multiple vars resolve to name {array_name:?}: {vars:?}"
                        ));
                    }
                }
            } else if let Some((obj_name, key)) = name.split_once('#') {
                let key = key.to_string();
                let json_value: Value = var.into();
                match body.get_mut(obj_name) {
                    None => {
                        body.insert(
                            obj_name.to_string(),
                            [(key, json_value)].into_iter().collect(),
                        );
                    }
                    Some(Value::Object(ref mut map)) => {
                        map.insert(key, json_value);
                    }
                    Some(_) => {
                        return Err(format!(
                            "multiple vars resolve to name {obj_name:?}: {vars:?}"
                        ));
                    }
                }
            } else {
                if body.contains_key(name) {
                    return Err(format!("multiple vars resolve to name {name:?}: {vars:?}"));
                }
                body.insert(name.to_string(), var.into());
            }
        }
        Ok(body)
    }

    /// # Errors
    /// * Returns `Err` when the request to the server fails.
    /// * Returns `Err` when the server returns a response other than 2xx or 4xx.
    /// # Panics
    /// Panics when it fails to build the target URL.
    pub fn rpc(&mut self, url: impl AsRef<str>) -> Result<bool, String> {
        let url = self.url.join(url.as_ref()).unwrap();
        let body = self.vars_json_body()?;
        println!("POST {url} {body:?}");
        let request = self.agent.request_url("POST", &url);
        let result = request.send_json(body);
        let opt_response = self.process_result(result)?;
        Ok(opt_response.is_some())
    }

    /// # Errors
    /// Returns `Err` when the variable is not a string.
    pub fn set_text(
        &mut self,
        var_name: impl AsRef<str>,
        text: impl AsRef<str>,
    ) -> Result<bool, String> {
        let var_name = var_name.as_ref();
        if let Some(Var::String(existing_text)) = self.vars.get(var_name) {
            if existing_text == text.as_ref() {
                return Ok(true);
            }
        }
        let widget = self.find_var(var_name)?;
        let poll_delay_ms = match widget {
            Widget::Checkbox(inner) => inner.poll_delay_ms,
            Widget::Selector(inner) => inner.poll_delay_ms,
            Widget::Textfield(inner) => inner.poll_delay_ms,
            other => {
                return Err(format!(
                    "cannot set text for widget of wrong type: {other:?}"
                ));
            }
        };
        let opt_prev_value = self
            .vars
            .insert(var_name.to_string(), Var::String(text.as_ref().to_string()));
        if let Some(prev_value) = opt_prev_value {
            let Var::String(..) = prev_value else {
                return Err(format!("set var {var_name:?} to string but it previously was a different type: {prev_value:?}"));
            };
        }
        if poll_delay_ms.is_some() {
            self.poll()
        } else {
            Ok(true)
        }
    }

    /// # Errors
    /// * Returns `Err` when a modal is visible.
    /// * Returns `Err` when one of the widget's actions returns `Err`.
    pub fn tap(&mut self, widget: Widget) -> Result<bool, String> {
        if self.modal.is_some() {
            return Err(format!(
                "tap called on widget while modal is shown: {:?}",
                self.modal
            ));
        }
        let actions = widget.actions()?.clone();
        match widget {
            Widget::Checkbox(inner) => {
                let initial_bool = inner.initial_bool;
                let var_name = inner.var_name.clone();
                let new_value = !self
                    .vars
                    .get(&var_name)
                    .cloned()
                    .unwrap_or(Var::Bool(initial_bool))
                    .bool()?;
                let opt_orig_value = self.vars.insert(var_name.clone(), Var::Bool(new_value));
                let success = self.do_actions(actions)?;
                if !success {
                    if let Some(orig_value) = opt_orig_value {
                        self.vars.insert(var_name, orig_value);
                    } else {
                        self.vars.remove(&var_name);
                    }
                }
                Ok(success)
            }
            _ => self.do_actions(actions),
        }
    }

    /// # Errors
    /// * Returns `Err` when the widget or modal button is not found.
    /// * Returns `Err` when one of the actions returns `Err`.
    pub fn tap_id(&mut self, id: impl AsRef<str>) -> Result<bool, String> {
        let id = id.as_ref();
        if let Some(modal) = &self.modal {
            let Some(button) = modal.buttons.iter().find(|b| b.id == id) else {
                return Err(format!("found no modal button with id {id:?}"));
            };
            let actions = button.actions.clone();
            self.modal = None;
            self.do_actions(actions)
        } else {
            self.tap(self.find_id(id)?.clone_shallow())
        }
    }

    /// # Errors
    /// * Returns `Err` when the widget or modal button is not found.
    /// * Returns `Err` when one of the actions returns `Err`.
    pub fn tap_text(&mut self, text: impl AsRef<str>) -> Result<bool, String> {
        let text = text.as_ref();
        if let Some(modal) = &self.modal {
            let Some(button) = modal.buttons.iter().find(|b| b.text.contains(text)) else {
                return Err(format!(
                    "found no modal button with text containing {text:?}"
                ));
            };
            let actions = button.actions.clone();
            self.modal = None;
            self.do_actions(actions)
        } else {
            self.tap(self.find_text(text)?.clone_shallow())
        }
    }

    /// # Errors
    /// * Returns `Err` when the widget or modal button is not found.
    /// * Returns `Err` when one of the actions returns `Err`.
    pub fn tap_var(&mut self, var_name: impl AsRef<str>) -> Result<bool, String> {
        self.tap(self.find_var(var_name)?.clone_shallow())
    }

    /// # Errors
    /// * Returns `Err` when a request to the server fails.
    /// * Returns `Err` when the server returns a response other than 2xx or 4xx.
    /// # Panics
    /// Panics when it fails to build the target URL.
    pub fn upload(
        &mut self,
        url: impl AsRef<str>,
        bytes: impl AsRef<[u8]>,
    ) -> Result<bool, String> {
        let url = self.url.join(url.as_ref()).unwrap();
        let bytes = bytes.as_ref();
        println!("PUT {url} body_len={}", bytes.len());
        let result = self.agent.request_url("PUT", &url).send_bytes(bytes);
        let opt_response = self.process_result(result)?;
        Ok(opt_response.is_some())
    }

    /// # Errors
    /// Returns `Err` when the page contains no widget with the specified variable.
    pub fn var(&self, var_name: impl AsRef<str>) -> Result<Var, String> {
        let var_name = var_name.as_ref();
        self.page()
            .vars()
            .into_iter()
            .filter(|(name, _initial)| *name == var_name)
            .map(|(name, initial)| self.vars.get(name).unwrap_or(&initial).clone())
            .next()
            .ok_or_else(|| format!("no widget found with var_name={var_name:?}"))
    }

    #[must_use]
    pub fn vars(&self) -> Vec<(String, Var)> {
        self.page()
            .vars()
            .into_iter()
            .map(|(name, initial)| {
                let var = self.vars.get(name).unwrap_or(&initial).clone();
                (name.to_string(), var)
            })
            .collect()
    }
}
