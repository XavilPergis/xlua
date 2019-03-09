use crate::span::Span;
use std::borrow::Cow;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Level {
    Note,
    Warn,
    Error,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Diagnostic {
    pub primary_span: Span,
    pub spans: Vec<Span>,
    pub level: Level,
    pub message: Option<Cow<'static, str>>,
    pub annotations: Vec<(Level, Cow<'static, str>)>,
}

impl From<Span> for Diagnostic {
    fn from(span: Span) -> Self {
        Diagnostic {
            primary_span: span,
            spans: vec![],
            level: Level::Error,
            message: None,
            annotations: vec![],
        }
    }
}

impl Diagnostic {
    pub fn with_level(mut self, level: Level) -> Self {
        self.level = level;
        self
    }

    pub fn with_message<T: Into<Cow<'static, str>>>(mut self, message: T) -> Self {
        self.message = Some(message.into());
        self
    }

    pub fn with_annotation<T: Into<Cow<'static, str>>>(mut self, level: Level, ann: T) -> Self {
        self.annotations.push((level, ann.into()));
        self
    }

    pub fn with_span(mut self, span: Span) -> Self {
        self.spans.push(span);
        self
    }
}
use ansi_term::{Color, Style};

fn level_style(level: Level) -> Style {
    match level {
        Level::Error => Color::Red.bold(),
        Level::Warn => Color::Yellow.bold(),
        Level::Note => Style::new().bold(),
    }
}

fn level_str(level: Level) -> &'static str {
    match level {
        Level::Error => "error",
        Level::Warn => "warning",
        Level::Note => "note",
    }
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct ErrorManager {
    err_spans: Vec<Diagnostic>,
}

impl ErrorManager {
    pub fn new() -> Self {
        ErrorManager { err_spans: vec![] }
    }

    pub fn span_error(&mut self, sp: Diagnostic) {
        self.err_spans.push(sp);
    }

    pub fn has_errors(&self) -> bool {
        self.err_spans.len() > 0
    }

    pub fn emit(&mut self, src: &str) {
        for diag in self.err_spans.drain(..) {
            let start = diag.primary_span.start;
            let end = diag.primary_span.end;
            let main_style = level_style(diag.level);

            print!(
                "{} at {}{}:{}{}",
                main_style.paint(level_str(diag.level)),
                Style::new().bold().prefix(),
                start.line + 1,
                start.column + 1,
                Style::new().bold().suffix(),
            );

            if let Some(message) = diag.message {
                print!(": {}", message);
            }

            println!();

            for (level, ann) in diag.annotations {
                println!(
                    " >> {}: {}",
                    level_style(level).paint(level_str(level)),
                    ann
                );
            }

            if start.line == end.line {
                let line = src.lines().skip(start.line).next().unwrap();
                let (before_painted, rest) = line.split_at(start.column);
                let (painted, rest) = rest.split_at(end.column - start.column);
                println!(" :: ");
                println!(
                    " :: {}{}{}{}{}",
                    before_painted,
                    main_style.prefix(),
                    painted,
                    main_style.suffix(),
                    rest,
                );
                print!(" :: ");
                for _ in 0..start.column {
                    print!(" ");
                }

                print!("{}", main_style.prefix());
                for _ in 0..end.column - start.column {
                    print!("~");
                }
                print!("{}", main_style.suffix());

                println!();
                println!();
            } else {
                let start_line = src.lines().skip(start.line).next().unwrap();
                let end_line = src.lines().skip(end.line).next().unwrap();
                let (unpainted, painted) = start_line.split_at(start.column);
                println!(" :: {}{}", unpainted, main_style.paint(painted));
                print!(" :: ");
                for _ in 0..start.column {
                    print!(" ");
                }
                println!("{}", main_style.paint("~ ->"));

                let (painted, unpainted) = end_line.split_at(end.column);
                println!(" :: {}{}", unpainted, main_style.paint(painted));
                print!(" :: ");
                for _ in 0..end.column {
                    print!(" ");
                }
                println!("{}", main_style.paint("~ <-"));
            }
        }
    }
}
