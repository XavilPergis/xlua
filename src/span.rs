use crate::error::Diagnostic;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct Index {
    pub line: usize,
    pub column: usize,
    pub byte: usize,
}

impl Index {
    pub fn advance_by(mut self, ch: char) -> Self {
        self.byte += ch.len_utf8();
        self.column += 1;

        if ch == '\n' {
            self.line += 1;
            self.column = 0;
        }

        self
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct Span {
    pub start: Index,
    pub end: Index,
}

impl Span {
    pub fn new(start: Index, end: Index) -> Self {
        debug_assert!(start.byte <= end.byte);
        Span { start, end }
    }

    pub fn advance_front(mut self, ch: char) -> Self {
        self.start.advance_by(ch);
        self
    }

    pub fn error_diagnostic(self) -> Diagnostic {
        self.into()
    }
}
