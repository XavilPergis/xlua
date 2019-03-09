use crate::error::Diagnostic;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct Index {
    pub line: usize,
    pub column: usize,
    pub byte: usize,
}

fn idx_min(a: Index, b: Index) -> Index {
    if a.byte < b.byte {
        a
    } else {
        b
    }
}

fn idx_max(a: Index, b: Index) -> Index {
    if a.byte > b.byte {
        a
    } else {
        b
    }
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

    pub fn shrink_n_same_line(mut self, n: usize) -> Self {
        self.start.byte += n;
        self.start.column += n;
        self.end.byte -= n;
        self.end.column -= n;
        self
    }

    pub fn byte_len(&self) -> usize {
        self.end.byte - self.start.byte
    }

    pub fn union(self, other: Span) -> Self {
        assert!(self.end.byte >= self.start.byte);

        let lo = idx_min(self.start, other.start);
        let hi = idx_max(self.end, other.end);

        Span { start: lo, end: hi }
    }

    pub fn error_diagnostic(self) -> Diagnostic {
        self.into()
    }
}
