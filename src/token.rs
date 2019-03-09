use crate::error::{ErrorManager, Level};
use crate::span::Index;
use crate::span::Span;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Keyword {
    And,
    Break,
    Do,
    Else,
    ElseIf,
    End,
    False,
    For,
    Function,
    Goto,
    If,
    In,
    Local,
    Nil,
    Not,
    Or,
    Repeat,
    Return,
    Then,
    True,
    Until,
    While,
}

impl Keyword {
    pub fn from_str(s: &str) -> Option<Self> {
        Some(match s {
            "and" => Keyword::And,
            "break" => Keyword::Break,
            "do" => Keyword::Do,
            "else" => Keyword::Else,
            "elseif" => Keyword::ElseIf,
            "end" => Keyword::End,
            "false" => Keyword::False,
            "for" => Keyword::For,
            "function" => Keyword::Function,
            "goto" => Keyword::Goto,
            "if" => Keyword::If,
            "in" => Keyword::In,
            "local" => Keyword::Local,
            "nil" => Keyword::Nil,
            "not" => Keyword::Not,
            "or" => Keyword::Or,
            "repeat" => Keyword::Repeat,
            "return" => Keyword::Return,
            "then" => Keyword::Then,
            "true" => Keyword::True,
            "until" => Keyword::Until,
            "while" => Keyword::While,

            _ => return None,
        })
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Token {
    Kw(Keyword),

    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Exp,
    Hash,
    BitAnd,
    Tilde,
    BitOr,
    LtLt,
    GtGt,
    ShashSlash,
    ColonColon,
    EqEq,
    TildeEq,
    LtEq,
    GtEq,
    Lt,
    Gt,
    Eq,

    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    OpenBracket,
    CloseBracket,

    Semicolon,
    Colon,
    Comma,
    Dot,
    DotDot,
    DotDotDot,

    Number,
    String(char),
    LongString(usize),
    Ident,
    Unknown(char),
}

#[macro_export]
#[cfg_attr(rustfmt, rustfmt_skip)]
macro_rules! tok {
    (and) => {Token::Kw(Keyword::And)};
    (break) => {Token::Kw(Keyword::Break)};
    (do) => {Token::Kw(Keyword::Do)};
    (else) => {Token::Kw(Keyword::Else)};
    (elseif) => {Token::Kw(Keyword::ElseIf)};
    (end) => {Token::Kw(Keyword::End)};
    (false) => {Token::Kw(Keyword::False)};
    (for) => {Token::Kw(Keyword::For)};
    (function) => {Token::Kw(Keyword::Function)};
    (goto) => {Token::Kw(Keyword::Goto)};
    (if) => {Token::Kw(Keyword::If)};
    (in) => {Token::Kw(Keyword::In)};
    (local) => {Token::Kw(Keyword::Local)};
    (nil) => {Token::Kw(Keyword::Nil)};
    (not) => {Token::Kw(Keyword::Not)};
    (or) => {Token::Kw(Keyword::Or)};
    (repeat) => {Token::Kw(Keyword::Repeat)};
    (return) => {Token::Kw(Keyword::Return)};
    (then) => {Token::Kw(Keyword::Then)};
    (true) => {Token::Kw(Keyword::True)};
    (until) => {Token::Kw(Keyword::Until)};
    (while) => {Token::Kw(Keyword::While)};

    (+) => {Token::Plus};
    (-) => {Token::Minus};
    (*) => {Token::Star};
    (/) => {Token::Slash};
    (%) => {Token::Percent};
    (^) => {Token::Exp};
    (#) => {Token::Hash};
    (&) => {Token::BitAnd};
    (~) => {Token::Tilde};
    (|) => {Token::BitOr};
    (<<) => {Token::LtLt};
    (>>) => {Token::GtGt};
    ("//") => {Token::ShashSlash};
    (::) => {Token::ColonColon};
    (==) => {Token::EqEq};
    (~=) => {Token::TildeEq};
    (<=) => {Token::LtEq};
    (>=) => {Token::GtEq};
    (<) => {Token::Lt};
    (>) => {Token::Gt};
    (=) => {Token::Eq};

    ("(") => {Token::OpenParen};
    (")") => {Token::CloseParen};
    ("{") => {Token::OpenBrace};
    ("}") => {Token::CloseBrace};
    ("[") => {Token::OpenBracket};
    ("]") => {Token::CloseBracket};

    (;) => {Token::Semicolon};
    (:) => {Token::Colon};
    (,) => {Token::Comma};
    (.) => {Token::Dot};
    (..) => {Token::DotDot};
    (...) => {Token::DotDotDot};
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct SpannedToken {
    pub ty: Token,
    pub span: Span,
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct Tokenizer<'src, 'ctx> {
    src: &'src str,
    idx: Index,

    errs: &'ctx mut ErrorManager,
}

impl<'a, 'b> Tokenizer<'a, 'b> {
    pub fn new(src: &'a str, errs: &'b mut ErrorManager) -> Self {
        Tokenizer {
            src,
            idx: Index::default(),
            errs,
        }
    }
}

impl Tokenizer<'_, '_> {
    /// Get the char at `n` chars offset from the current cursor.
    fn next(&self, n: usize) -> Option<char> {
        self.src[self.idx.byte..].chars().skip(n).next()
    }

    /// Advance the cursor by the size of `ch` and update like number and column number.
    fn consume_char(&mut self, ch: char) {
        self.idx = self.idx.advance_by(ch);
    }

    /// Bump the cursor `n` chars from the input. Panics if the end of the input is reached.
    fn consume(&mut self, n: usize) {
        for _ in 0..n {
            self.consume_char(self.next(0).expect("Tried consuming past the end of input"));
        }
    }

    fn make_token(&self, start: Index, ty: Token) -> SpannedToken {
        SpannedToken {
            ty,
            span: Span::new(start, self.idx),
        }
    }

    /// Consume characters until a non-whitespace char.
    fn scan_whitespace(&mut self) {
        while self.next(0).map(char::is_whitespace).unwrap_or(false) {
            self.consume(1);
        }
    }

    fn scan_while<F>(&mut self, mut func: F) -> usize
    where
        F: FnMut(char) -> bool,
    {
        let mut scanned = 0;
        while self.next(0).map(|ch| func(ch)).unwrap_or(false) {
            self.consume(1);
            scanned += 1;
        }
        scanned
    }

    fn scan_while_max<F>(&mut self, max: usize, mut func: F) -> usize
    where
        F: FnMut(char) -> bool,
    {
        let mut scanned = 0;
        while self.next(0).map(|ch| func(ch)).unwrap_or(false) && max > scanned {
            self.consume(1);
            scanned += 1;
        }
        scanned
    }

    // TODO: is this correct? this matches `0.` as a `Float`
    fn scan_number(&mut self, radix: u32) -> Token {
        self.scan_while(|ch| ch.is_digit(radix));
        match self.next(0) {
            Some('.') => {
                self.consume(1);
                self.scan_while(|ch| ch.is_digit(radix));
                Token::Number
            }
            _ => Token::Number,
        }
    }

    /// Consume one char if `ch` is the same as the input stream, returning true if so.
    /// Otherwise, don't do anything and return false.
    fn eat(&mut self, ch: char) -> bool {
        match self.next(0) {
            Some(c) if c == ch => {
                self.consume_char(c);
                true
            }
            _ => false,
        }
    }

    fn scan_unicode_delim(&mut self, delim: char, escape_start: Index) -> bool {
        match self.next(0) {
            Some(ch) if ch == delim => {
                self.consume(1);
                true
            }

            Some(ch) => {
                self.errs.span_error(
                    Span::new(self.idx, self.idx.advance_by(ch))
                        .error_diagnostic()
                        .with_message("malformed unicode escape sequence")
                        .with_annotation(
                            Level::Note,
                            format!(
                                "I was looking for a `{}`, but I found `{}` instead",
                                delim, ch
                            ),
                        ),
                );
                false
            }

            None => {
                self.errs.span_error(
                    Span::new(escape_start, self.idx)
                        .error_diagnostic()
                        .with_message("malformed unicode escape sequence")
                        .with_annotation(Level::Note, "The file unexpectedly ended while I was parsing a unicode escape sequence!"),
                );
                false
            }
        }
    }

    fn scan_unicode_escape(&mut self, escape_start: Index) {
        if !self.scan_unicode_delim('{', escape_start) {
            return;
        }
        self.scan_while(|ch| ch.is_digit(16));
        if !self.scan_unicode_delim('}', escape_start) {
            return;
        }
    }

    fn scan_hex_escape_digit(&mut self, escape_start: Index) -> bool {
        let digit_start = self.idx;
        match self.next(0) {
            // This is what we want, advance
            Some(ch) if ch.is_digit(16) => {
                self.consume(1);
                true
            }

            Some(ch) => {
                self.errs.span_error(
                    Span::new(digit_start, self.idx.advance_by(ch))
                        .error_diagnostic()
                        .with_message("malformed hex escape sequence")
                        .with_annotation(
                            Level::Note,
                            format!(
                                "I was looking for a hex digit, but I found `{}` instead",
                                ch
                            ),
                        )
                        .with_annotation(
                            Level::Note,
                            "`\\x` has to be followed by exactly two hex digits",
                        ),
                );
                false
            }

            None => {
                self.errs.span_error(
                    Span::new(escape_start, self.idx)
                        .error_diagnostic()
                        .with_message("unterminated hex escape sequence"),
                );
                false
            }
        }
    }

    fn scan_hex_escape(&mut self, escape_start: Index) {
        // Consume two hex digits.
        for _ in 0..2 {
            if !self.scan_hex_escape_digit(escape_start) {
                return;
            }
        }
    }

    // NOTE: this assumes that the cursor is at a number.
    fn scan_dec_escape(&mut self) {
        debug_assert!(self.next(0).expect("dec escape missing digit").is_digit(10));
        self.scan_while_max(3, |ch| ch.is_digit(10));
    }

    fn scan_escape_sequence(&mut self, escape_start: Index) {
        match self.next(0) {
            Some(ch) => match ch {
                // Normal escape sequence, sonsume it and move on.
                'a' | 'b' | 'f' | 'n' | 'r' | 't' | 'v' | '\\' | '"' | '\'' | '\r' | '\n' => {
                    self.consume(1);
                }

                // Unicode escape, like `\u{CODEPOINT}`
                'u' => {
                    self.consume(1);
                    self.scan_unicode_escape(escape_start);
                }

                // Hex escape, like `\xNN`
                'x' => {
                    // consume the `x`
                    self.consume(1);
                    self.scan_hex_escape(escape_start);
                }

                ch if ch.is_digit(10) => {
                    self.scan_dec_escape();
                }

                ch => self.errs.span_error(
                    Span::new(escape_start, self.idx)
                        .error_diagnostic()
                        .with_message("unknown escape code")
                        .with_annotation(
                            Level::Note,
                            format!("I was looking for an escape code, but I found `{}` which is not one", ch),
                        ),
                ),
            },

            None => self.errs.span_error(
                Span::new(escape_start, self.idx)
                    .error_diagnostic()
                    .with_message("unterminated escape sequence"),
            ),
        }
    }

    // TODO: escapes
    // Either scan a normal char, or if the cursor is on a `\`, scan past the end of the escape sequence. We do this so
    // that we can have strings like "\"", because otherwise the escaped `"` would be read and the string would terminate early.
    fn scan_string_char(&mut self) {
        match self.next(0) {
            Some('\\') => {
                let escape_start = self.idx;
                self.consume(1);
                self.scan_escape_sequence(escape_start);
            }
            Some(_) => {
                self.consume(1);
            }
            _ => {}
        }
    }

    fn scan_string(&mut self, quote_char: char) {
        let start = self.idx;

        // Eat the opening string char. This isn't really needed for how we call this, since we already know that the
        // we have the correct opening char, but this is just for completeness.
        if !self.eat(quote_char) {
            return;
        }

        loop {
            match self.next(0) {
                // If our cursor is over the same char we opened with, then we found the end of the string.
                Some(ch) if ch == quote_char => break,
                Some(_) => self.scan_string_char(),

                // If we get to the end of the file while scanning a string, then we have an unterminated string.
                None => {
                    self.errs.span_error(
                        Span::new(start, self.idx).error_diagnostic().with_message(
                            match quote_char {
                                '"' => "unterminated double quote string".into(),
                                '\'' => "unterminated single quote string".into(),
                                k => format!("unterminated `{}`-delimited string", k),
                            },
                        ),
                    );
                    return;
                }
            }
        }

        // Consume the string terminator. We know this is the same as the opening char because the only way we break
        // out of the loop is by matching the start char.
        self.consume(1);
    }

    fn scan_raw_string(&mut self) -> usize {
        debug_assert!(self.next(0) == Some('['));
        let start = self.idx;
        self.consume(1);
        let level = self.scan_while(|ch| ch == '=');
        // The two brackets plus the number of `=`s
        let delim_len = level + 2;

        if !self.eat('[') {
            self.errs.span_error(
                Span::new(start, self.idx)
                    .error_diagnostic()
                    .with_message("malformed long string")
                    .with_annotation(
                        Level::Note,
                        "I was looking for a `[`, but I did not find one",
                    ),
            );
            return delim_len;
        }

        loop {
            match self.next(0) {
                // We want to find a sequence like `]==]` with a matching number of `=` as the level.
                Some(']') => {
                    // consume the first `]`
                    self.consume(1);
                    let found = self.scan_while(|ch| ch == '=');
                    // If the number of `=`s matches, then try to consume a `]`, otherwise just ignore the whole thing and continue scanning the string.
                    if found == level {
                        // Correct formatting, exit the loop.
                        if self.next(0) == Some(']') {
                            self.consume(1);
                            return delim_len;
                        }
                    }
                }
                // Other char, scan the char/escape
                Some(_) => self.scan_string_char(),
                None => {
                    self.errs.span_error(
                        Span::new(start, self.idx)
                            .error_diagnostic()
                            .with_message(format!("unterminated {}-level long string", level)),
                    );
                    return delim_len;
                }
            }
        }
    }

    // -- line comment
    // --[[ block comment ]]
    // NOTE: block comments cannot nest :(
    fn scan_comment(&mut self) {
        let comment_start = self.idx;
        match (self.next(0), self.next(1)) {
            (Some('-'), Some('-')) => self.consume(2),
            _ => return,
        }

        match (self.next(0), self.next(1)) {
            // This is a block comment; scan until we find `]]`. Also, it doesn't seem like block comments nest...
            (Some('['), Some('[')) => {
                self.consume(2);
                loop {
                    match self.next(0) {
                        // If the next two chars are `]]` then consume them.
                        Some(']') => match self.next(1) {
                            Some(']') => {
                                self.consume(2);
                                break;
                            }
                            // Just consume the `-` we matched.
                            _ => self.consume(1),
                        },

                        // If we get to the end of the file and we're still looking for the end of a block comment,
                        // then we have an unterminated block comment. Error and break out of the loop.
                        None => {
                            self.errs.span_error(
                                Span::new(comment_start, self.idx)
                                    .error_diagnostic()
                                    .with_message("unterminated block comment"),
                            );
                            break;
                        }

                        // Advance one for every other char.
                        _ => self.consume(1),
                    }
                }
            }

            // This is a line comment; scan to the end of the line.
            _ => {
                while self.next(0).map(|ch| ch != '\n').unwrap_or(false) {
                    self.consume(1);
                }
            }
        }
    }

    // The main driver function; The tokenizer advances one token with each call, skipping whitespace and comments if it needs to.
    pub fn scan(&mut self) -> Option<SpannedToken> {
        // Scan leading whitespace away, so the cursor is at a char that is *not* whitespace.
        self.scan_whitespace();

        let start_idx = self.idx;
        let ch = self.next(0)?;

        // Match an identifier or keyword. Idents look like `<id_start> <id_continue>*`
        if is_ident_start(ch) {
            while self.next(0).map(is_ident_continue).unwrap_or(false) {
                self.consume(1);
            }

            // Find the actual identifier text. If the ident is a keyword, emit the matching keyword token instead.
            let lexeme = &self.src[start_idx.byte..self.idx.byte];
            return Some(
                self.make_token(
                    start_idx,
                    Keyword::from_str(lexeme)
                        .map(Token::Kw)
                        .unwrap_or(Token::Ident),
                ),
            );
        }

        // Match a number. FIXME: this might be a little touchy...
        if ch.is_digit(10) {
            if self.next(1) == Some('x') {
                self.consume(2);
                let tt = self.scan_number(16);
                return Some(self.make_token(start_idx, tt));
            } else {
                let tt = self.scan_number(10);
                return Some(self.make_token(start_idx, tt));
            }
        }

        // Consume 1 char and return the specified token
        macro_rules! tok1 {
            ($tok:ident) => {{
                self.consume(1);
                Token::$tok
            }};
        }

        // Consume a char and pick the correct token depending on the next char. If the token is 2 chars long, consume
        // the second char too.
        macro_rules! tok2 {
            ($single:ident, [$($ch:tt = $tok:ident),+]) => {{
                self.consume(1);
                match self.next(0) {
                    $(Some($ch) => {
                        self.consume(1);
                        Token::$tok
                    },)+
                    _ => Token::$single
                }
            }};
        }

        let tok = match ch {
            '+' => tok1!(Plus),
            '*' => tok1!(Star),
            '%' => tok1!(Percent),
            '^' => tok1!(Exp),
            '#' => tok1!(Hash),
            '&' => tok1!(BitAnd),
            '|' => tok1!(BitOr),
            ';' => tok1!(Semicolon),
            ',' => tok1!(Comma),

            '(' => tok1!(OpenParen),
            ')' => tok1!(CloseParen),
            '{' => tok1!(OpenBrace),
            '}' => tok1!(CloseBrace),
            ']' => tok1!(CloseBracket),

            '~' => tok2!(Tilde, ['=' = TildeEq]),
            '/' => tok2!(Slash, ['/' = ShashSlash]),
            '=' => tok2!(Eq, ['=' = EqEq]),
            ':' => tok2!(Colon, [':' = ColonColon]),
            '<' => tok2!(Lt, ['<' = LtLt, '=' = LtEq]),
            '>' => tok2!(Gt, ['>' = GtGt, '=' = GtEq]),

            '[' => match self.next(1) {
                Some('[') | Some('=') => {
                    let level = self.scan_raw_string();
                    Token::LongString(level)
                }
                _ => {
                    self.consume(1);
                    Token::OpenBracket
                }
            },

            // Either match a `Minus` token or a comment.
            '-' => match self.next(1) {
                // If the char after the first is also a `-` then we have some sort of comment.
                // Basically, it consumes `<comment> <token>` but only returns `<token>`. Note that `<token>` can be a
                // comment itself, so it really consumes `<comment>* <token>`.
                Some('-') => {
                    self.scan_comment();
                    return self.scan();
                }
                _ => {
                    self.consume(1);
                    Token::Minus
                }
            },

            '.' => {
                self.consume(1);
                match (self.next(0), self.next(1)) {
                    (Some('.'), Some('.')) => {
                        self.consume(2);
                        Token::DotDotDot
                    }

                    (Some('.'), _) => {
                        self.consume(1);
                        Token::DotDot
                    }

                    _ => Token::Dot,
                }
            }

            // Scan each type of string.
            '"' => {
                self.scan_string('"');
                Token::String('"')
            }
            '\'' => {
                self.scan_string('\'');
                Token::String('\'')
            }

            ch => {
                self.consume(1);
                self.errs.span_error(
                    Span::new(start_idx, start_idx.advance_by(ch))
                        .error_diagnostic()
                        .with_message("unknown token"),
                );
                Token::Unknown(ch)
            }
        };

        Some(self.make_token(start_idx, tok))
    }
}

fn is_in_range(ch: char, lo: char, hi: char) -> bool {
    ch >= lo && ch <= hi
}

fn is_ident_start(ch: char) -> bool {
    // ch.is_xid_start() || ch == '_'
    is_in_range(ch, 'a', 'z') || is_in_range(ch, 'A', 'Z') || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    // ch.is_xid_continue()
    is_in_range(ch, 'a', 'z') || is_in_range(ch, 'A', 'Z') || is_in_range(ch, '0', '9') || ch == '_'
}
