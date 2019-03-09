use crate::error::ErrorManager;
use crate::error::Level;
use crate::span::Index;
use crate::span::Span;
// use crate::token::tok;
use crate::token::SpannedToken;
use crate::token::{Keyword, Token};

pub type List<T> = Vec<T>;
pub type Name = String;

#[derive(Clone, Debug, PartialEq)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub return_statement: Option<List<Expr>>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Lhs {
    Ident(Name),
    Index(Box<Expr>, Box<Expr>),
}

// foo.bar:baz(quux)
// foo.bar.baz(foo.bar, quux)

// NOTE: `func "foo"` and `func {a=1}` are translated to a call with one arg.
#[derive(Clone, Debug, PartialEq)]
pub enum Call {
    /// Normal function call: `foo.bar(baz)`. Tuple of the function being called and the list of arguments.
    Function(Box<Expr>, List<Expr>),
    /// Method call: `foo.bar:baz(quux)`. Tuple of the object the method is being called on, the method name, and the
    /// list of arguments.
    Method(Box<Expr>, Name, List<Expr>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExprAndBlock {
    pub cond: Expr,
    pub block: Block,
}

#[derive(Clone, Debug, PartialEq)]
pub enum For {
    /// "for" <name> "=" <expr> "," <expr> ("," <expr>)? "do" <block> "end"
    Numeric {
        /// The variable that gets changed each iteration.
        binding: Name,
        /// The start value for the loop.
        start: Expr,
        /// The end value for the loop.
        end: Expr,
        /// An optional step, otherwise it is a step of 1
        step: Option<Expr>,
        /// The code that's executed each iteration.
        block: Block,
    },

    /// "for" <list[<name>]> "in" <list[<name>]> "do" <block> "end"
    Generic {
        /// The variables that gets changed each iteration.
        bindings: List<Name>,
        /// The list of expressions that update the bindings each iteration.
        iterators: List<Expr>,
        /// The code that's executed each iteration.
        block: Block,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct If {
    pub if_clause: ExprAndBlock,
    pub elseif_clauses: List<ExprAndBlock>,
    pub else_clause: Option<Block>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Func {
    pub params: List<Name>,
    pub body: Block,
    pub varadic: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
    // NOTE: function decls need to be translated to this node as per 3.4.11
    Assign(List<Lhs>, List<Expr>),
    Local(List<Name>, Option<List<Expr>>),
    LocalFunc(Name, Func),
    Call(Call),

    Goto(Name),
    Label(Name),
    Do(Block),
    While(ExprAndBlock),
    Repeat(ExprAndBlock),
    Break,

    If(If),
    For(For),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Nil,
    True,
    False,
    Varargs,

    Number(f64),
    String(String),

    /// Closure expression. List of arguments, function body, whether or not the function is varadic.
    Func(Func),
    Table(List<TableEntry>),
    BinOp(Box<Expr>, BinOp, Box<Expr>),
    UnOp(UnOp, Box<Expr>),
    // foo or foo.bar or foo[bar]
    Lhs(Lhs),
    // foo(a, b) or x:z(a, b)
    Call(Call),
    // `return a, func()` vs `return a, (func())` when `func()` return multiple vals
    Paren(Box<Expr>),
}

// [key] = val
//
//     val ->   [i] = val
// k = val -> ["k"] = val
#[derive(Clone, Debug, PartialEq)]
pub struct TableEntry {
    pub key: Expr,
    pub val: Expr,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinOp {
    // Numbers
    Add,
    Sub,
    Mul,
    Div,
    FloorDiv,
    Exp,
    Mod,

    // Numbers (bitwise)
    BitAnd,
    BitXor,
    BitOr,
    BitShr,
    BitShl,

    // Strings
    Concat,

    // Comparison/bools
    Less,
    LessEq,
    Greater,
    GreaterEq,
    Eq,
    NotEq,
    And,
    Or,
}

impl BinOp {
    /// Binary operator precedence
    fn precedence(&self) -> usize {
        use self::BinOp::*;
        match self {
            Or => 0,
            And => 1,

            Less | LessEq | Greater | GreaterEq | Eq | NotEq => 2,

            BitOr => 3,
            BitXor => 4,
            BitAnd => 5,
            BitShr | BitShl => 6,
            Concat => 7,

            Add | Sub => 8,
            Mul | Div | FloorDiv | Mod => 9,
            Exp => 10,
        }
    }

    fn is_right_assoc(&self) -> bool {
        match self {
            BinOp::Concat | BinOp::Exp => true,
            _ => false,
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnOp {
    Minus,
    Not,
    Length,
    BitNot,
}

pub struct Parser<'src, 'ctx> {
    // FIXME: use a string pool/interner or something lol
    src: &'src str,
    tokens: &'src [SpannedToken],
    idx: usize,

    dbg_spaces: usize,

    errs: &'ctx mut ErrorManager,
}

impl<'src, 'ctx> Parser<'src, 'ctx> {
    pub fn new(src: &'src str, tokens: &'src [SpannedToken], errs: &'ctx mut ErrorManager) -> Self {
        Parser {
            src,
            tokens,
            idx: 0,
            dbg_spaces: 0,
            errs,
        }
    }

    fn dbg_pad(&self) {
        for _ in 0..self.dbg_spaces {
            print!("  ");
        }
    }

    fn check(&self, tok: Token) -> bool {
        self.idx < self.tokens.len() && self.tokens[self.idx].ty == tok
    }

    fn check_lookahead(&self, lookahead: usize, tok: Token) -> bool {
        self.idx + lookahead < self.tokens.len() && self.tokens[self.idx + lookahead].ty == tok
    }

    fn eat(&mut self, expect: bool, tok: Token) -> Option<()> {
        if self.check(tok) {
            self.bump();
            Some(())
        } else {
            if expect {
                self.expect_err(tok);
            }
            None
        }
    }

    fn get_text(&self) -> Option<&'src str> {
        let span = self.next()?.span;
        Some(&self.src[span.start.byte..span.end.byte])
    }

    fn expect_err<T: std::fmt::Debug>(&mut self, item: T) {
        self.dbg_pad();
        println!(
            "\x1b[31m@! bad expect {:?} / {:?}\x1b[0m",
            item,
            self.next().map(|t| t.ty)
        );
        match self.next() {
            Some(next) => self.errs.span_error(
                next.span
                    .error_diagnostic()
                    .with_message("unexpected token")
                    .with_annotation(
                        Level::Note,
                        format!(
                            "I was looking for `{:?}`, but I found `{:?}` instead.",
                            item, next.ty
                        ),
                    ),
            ),
            None => {
                // self.errs.span_error(
                //     Span::new(self.char_start, self.idx)
                //         .error_diagnostic()
                //         .with_message("invalid codepoint")
                //         .with_annotation(Level::Note, format!("I was looking for a valid codepoint but I found a codepoint with the value of `{}`.", codepoint)),
                // )
            }
        }
    }

    fn next(&self) -> Option<&'src SpannedToken> {
        self.tokens.get(self.idx)
    }

    fn lookahead(&self, lookahead: usize) -> Option<&'src SpannedToken> {
        self.tokens.get(self.idx + lookahead)
    }

    fn bump(&mut self) {
        self.dbg_pad();
        println!("\x1b[32m@ bumped {:?}\x1b[0m", self.tokens[self.idx].ty);
        self.idx += 1;
    }

    fn consume(&mut self, num_tokens: usize) {
        self.dbg_pad();
        println!(
            "\x1b[33m@ bumped {} tokens ({:?})\x1b[0m",
            num_tokens,
            &self.tokens[self.idx..self.idx + num_tokens]
        );
        self.idx += num_tokens;
    }

    fn eat_ident(&mut self, expect: bool) -> Option<&'src str> {
        if self.check(Token::Ident) {
            let span = self.next()?.span;
            self.bump();
            Some(&self.src[span.start.byte..span.end.byte])
        } else {
            if expect {
                self.expect_err("ident");
            }
            None
        }
    }

    fn tok_err(&mut self, header: &'static str, annotations: impl IntoIterator<Item = String>) {
        if let Some(tok) = self.next() {
            let mut msg = tok.span.error_diagnostic().with_message(header);
            for ann in annotations {
                msg = msg.with_annotation(Level::Note, ann);
            }
            self.errs.span_error(msg);
        }
    }

    fn span_err(
        &mut self,
        span: Span,
        header: &'static str,
        annotations: impl IntoIterator<Item = String>,
    ) {
        let mut msg = span.error_diagnostic().with_message(header);
        for ann in annotations {
            msg = msg.with_annotation(Level::Note, ann);
        }
        self.errs.span_error(msg);
    }

    fn span_union_err(
        &mut self,
        span: Span,
        header: &'static str,
        annotations: impl IntoIterator<Item = String>,
    ) {
        if let Some(tok) = self.next() {
            let mut msg = span.union(tok.span).error_diagnostic().with_message(header);
            for ann in annotations {
                msg = msg.with_annotation(Level::Note, ann);
            }
            self.errs.span_error(msg);
        }
    }
}

macro_rules! dbg_wrap {
    ($self:ident, $name:expr, $closure:expr) => {{
        $self.dbg_pad();
        println!("+ {}", $name);
        $self.dbg_spaces += 1;
        let ret = $closure();
        $self.dbg_spaces -= 1;
        // $self.dbg_pad();
        // println!("< {}", $name);
        ret
    }};
}

impl Parser<'_, '_> {
    // chunk := <block> ;;
    pub fn p_chunk(&mut self) -> Option<Block> {
        dbg_wrap!(self, "p_chunk", || {
            let block = self.p_block();
            if self.next().is_some() {
                self.tok_err(
                    "incomplete parse",
                    vec!["I tried parsing the whole file but only got part way through".into()],
                );
                None
            } else {
                Some(block)
            }
        })
    }

    // block := <stat>* <retstat>? ;;
    fn p_block(&mut self) -> Block {
        dbg_wrap!(self, "p_block", || {
            let mut statements = vec![];
            while let Some(stmt) = self.p_stat() {
                statements.push(stmt);
            }
            let return_statement = self.p_retstat(false);

            Block {
                statements,
                return_statement,
            }
        })
    }

    // stat := ";"
    // 	     | "break"
    // 	     | "goto" :name
    // 	     | "do" <block> "end"
    // 	     | "while" <exp> "do" <block> "end"
    // 	     | "repeat" <block> "until" <exp>
    // 	     | "function" <funcname> <funcbody>
    // 	     | "local" "function" :name <funcbody>
    // 	     | "local" <namelist> ("=" explist)?
    // 	     | <label>
    // 	     | <if_stmt>
    // 	     | <for_stmt>
    // 	     | <varlist> "=" <explist>
    // 	     | <functioncall> ;;
    fn p_stat(&mut self) -> Option<Statement> {
        dbg_wrap!(self, "p_stat", || {
            let next = self.next()?;
            Some(match next.ty {
                Token::Semicolon => {
                    self.bump();
                    return self.p_stat();
                }
                Token::Kw(Keyword::Break) => {
                    self.bump();
                    Statement::Break
                }
                Token::Kw(Keyword::Goto) => {
                    self.bump();
                    if let Some(ident) = self.eat_ident(false) {
                        Statement::Goto(ident.into())
                    } else {
                        self.tok_err(
                            "invalid goto target",
                            vec!["I can't jump to anything other than a label name!".into()],
                        );
                        self.p_stat()?
                    }
                }
                Token::Kw(Keyword::Do) => {
                    self.bump();
                    let block = self.p_block();
                    self.eat(true, Token::Kw(Keyword::End))?;
                    Statement::Do(block)
                }
                Token::Kw(Keyword::While) => {
                    self.bump();
                    let cond = self.p_exp(true)?;
                    self.eat(true, Token::Kw(Keyword::Do))?;
                    let block = self.p_block();
                    self.eat(true, Token::Kw(Keyword::End))?;
                    Statement::While(ExprAndBlock { cond, block })
                }
                Token::Kw(Keyword::Repeat) => {
                    self.bump();
                    let block = self.p_block();
                    self.eat(true, Token::Kw(Keyword::Until))?;
                    let cond = self.p_exp(true)?;
                    Statement::Repeat(ExprAndBlock { cond, block })
                }
                // The colon syntax is used for defining methods, that is, functions that have an implicit extra parameter self. Thus, the statement
                //     function t.a.b.c:f (params) body end
                // is syntactic sugar for
                //     t.a.b.c.f = function (self, params) body end
                Token::Kw(Keyword::Function) => {
                    self.bump();
                    let (lhs_path, method) = self.p_funcname(true)?;
                    let mut body = self.p_funcbody(true)?;

                    // If this is a method, add `self` as the first param
                    if method.is_some() {
                        body.params.insert(0, "self".into());
                    }

                    fn path_to_lhs(mut path: List<Name>) -> Lhs {
                        match path.len() {
                            0 => unreachable!(
                                "Should not be able to have a function decl without a path"
                            ),
                            1 => Lhs::Ident(path.pop().unwrap()),
                            _ => {
                                let idx = path.pop().unwrap();
                                Lhs::Index(
                                    Box::new(Expr::Lhs(path_to_lhs(path))),
                                    Box::new(Expr::String(idx)),
                                )
                            }
                        }
                    }

                    let lhs = path_to_lhs(lhs_path);
                    let lhs = if let Some(ident) = method {
                        Lhs::Index(Box::new(Expr::Lhs(lhs)), Box::new(Expr::String(ident)))
                    } else {
                        lhs
                    };

                    Statement::Assign(vec![lhs], vec![Expr::Func(body)])
                }
                Token::Kw(Keyword::Local) => {
                    self.bump();
                    if self.eat(false, Token::Kw(Keyword::Function)).is_some() {
                        let ident = self.eat_ident(true)?.into();
                        let body = self.p_funcbody(true)?;
                        Statement::LocalFunc(ident, body)
                    } else {
                        let names = self.p_namelist(true)?;
                        let vals = if self.eat(false, Token::Eq).is_some() {
                            Some(self.p_explist(true)?)
                        } else {
                            None
                        };
                        Statement::Local(names, vals)
                    }
                }
                Token::ColonColon => Statement::Label(self.p_label(true)?),
                Token::Kw(Keyword::If) => Statement::If(self.p_if_stat(true)?),
                Token::Kw(Keyword::For) => Statement::For(self.p_for_stat(true)?),

                Token::Ident => {
                    let list_start = self.next().unwrap().span;
                    // starts with an ident so it's either an assignment or a function call...
                    // if we are looking at a var list, then we have `<lhs> ","` or `<lhs> "="`.
                    // Otherwise, we have `<expr> "(" <explist> ")"`
                    let expr = self.p_exp(true)?;

                    match expr {
                        // We have an lhs, but it might be the start of a list of assignables.
                        // If the next token is an `=`, then we have a single element list.
                        // If the next token is a `,`, then we have more than a single lhs.
                        Expr::Lhs(lhs) => {
                            let mut assignables = vec![lhs];

                            if self.eat(false, Token::Comma).is_some() {
                                let list = self.p_varlist(true);
                                match list {
                                    Some(list) => assignables.extend(list),
                                    None => self.span_union_err(
                                        list_start,
                                        "invalid expression list",
                                        vec!["".into()],
                                    ),
                                }
                            }
                            self.eat(true, Token::Eq)?;
                            let exprs = self.p_explist(true)?;

                            Statement::Assign(assignables, exprs)
                        }
                        Expr::Call(call) => Statement::Call(call),
                        _ => unimplemented!(),
                    }
                }

                _ => return None,
            })
        })
    }

    // if_stmt  := "if" <exp> "then" <block> ("elseif" <exp> "then" <block>)* ("else" <block>)? "end" ;;
    fn p_if_stat(&mut self, expect: bool) -> Option<If> {
        dbg_wrap!(self, "p_if_stat", || {
            self.eat(expect, Token::Kw(Keyword::If))?;
            let cond = self.p_exp(true)?;
            self.eat(true, Token::Kw(Keyword::Then))?;
            let block = self.p_block();
            let if_clause = ExprAndBlock { cond, block };

            let mut elseif_clauses = vec![];
            while self.eat(false, Token::Kw(Keyword::ElseIf)).is_some() {
                let cond = self.p_exp(true)?;
                self.eat(true, Token::Kw(Keyword::Then))?;
                let block = self.p_block();
                elseif_clauses.push(ExprAndBlock { cond, block })
            }

            let else_clause = if self.eat(false, Token::Kw(Keyword::Else)).is_some() {
                Some(self.p_block())
            } else {
                None
            };

            self.eat(true, Token::Kw(Keyword::End))?;
            Some(If {
                if_clause,
                elseif_clauses,
                else_clause,
            })
        })
    }

    // for_stmt := "for" :name "=" <exp> "," <exp> ("," <exp>)? "do" <block> "end"
    // 	         | "for" <namelist> "in" <explist> "do" <block> "end" ;;
    fn p_for_stat(&mut self, expect: bool) -> Option<For> {
        dbg_wrap!(self, "p_for_stat", || {
            self.eat(expect, Token::Kw(Keyword::For))?;
            Some(if self.check_lookahead(1, Token::Eq) {
                // numerical for loop
                let binding = self.eat_ident(true)?.into();
                self.eat(true, Token::Eq)?;
                let start = self.p_exp(true)?;
                self.eat(true, Token::Comma)?;
                let end = self.p_exp(true)?;
                let step = if self.eat(false, Token::Comma).is_some() {
                    Some(self.p_exp(true)?)
                } else {
                    None
                };
                self.eat(true, Token::Kw(Keyword::Do))?;
                let block = self.p_block();
                self.eat(true, Token::Kw(Keyword::End))?;

                For::Numeric {
                    binding,
                    start,
                    end,
                    step,
                    block,
                }
            } else {
                let bindings = self.p_namelist(true)?;
                self.eat(true, Token::Kw(Keyword::In))?;
                let iterators = self.p_explist(true)?;
                self.eat(true, Token::Kw(Keyword::Do))?;
                let block = self.p_block();
                self.eat(true, Token::Kw(Keyword::End))?;
                For::Generic {
                    bindings,
                    iterators,
                    block,
                }
            })
        })
    }

    // retstat := "return" <explist>? ";"? ;;
    fn p_retstat(&mut self, expect: bool) -> Option<List<Expr>> {
        dbg_wrap!(self, "p_retstat", || {
            self.eat(expect, Token::Kw(Keyword::Return))?;
            // TODO: is not expecting correct here?
            let exprs = self.p_explist(false)?;
            let _ = self.eat(false, Token::Semicolon);
            Some(exprs)
        })
    }

    // label := "::" :name "::" ;;
    fn p_label(&mut self, expect: bool) -> Option<Name> {
        dbg_wrap!(self, "p_label", || {
            self.eat(expect, Token::ColonColon)?;
            let name = self.eat_ident(true)?;
            self.eat(true, Token::ColonColon)?;
            Some(name.into())
        })
    }

    // funcname := :name ("." :name)* (":" :name)? ;;
    fn p_funcname(&mut self, expect: bool) -> Option<(List<Name>, Option<Name>)> {
        dbg_wrap!(self, "p_funcname", || {
            let mut path = vec![self.eat_ident(expect)?.into()];

            while self.eat(false, Token::Dot).is_some() {
                path.push(self.eat_ident(true)?.into());
            }

            let method = if self.eat(false, Token::Colon).is_some() {
                Some(self.eat_ident(true)?.into())
            } else {
                None
            };

            Some((path, method))
        })
    }

    // varlist := <var> ("," <var>)* ;;
    fn p_varlist(&mut self, expect: bool) -> Option<List<Lhs>> {
        dbg_wrap!(self, "p_varlist", || self
            .p_list_generic(expect, |p, e| p.p_var(e)))
    }

    // namelist := :name ("," :name)* ;;
    fn p_namelist(&mut self, expect: bool) -> Option<List<Name>> {
        dbg_wrap!(self, "p_namelist", || self
            .p_list_generic(expect, |p, e| p.eat_ident(e).map(Into::into)))
    }

    // explist := <exp> ("," <exp>)* ;;
    fn p_explist(&mut self, expect: bool) -> Option<List<Expr>> {
        dbg_wrap!(self, "p_explist", || self
            .p_list_generic(expect, |p, e| p.p_exp(e)))
    }

    fn p_list_generic<T, F>(&mut self, expect: bool, mut func: F) -> Option<List<T>>
    where
        F: FnMut(&mut Self, bool) -> Option<T>,
    {
        // dbg_wrap!(self, "p_for_stat", || {
        let mut list = vec![func(self, expect)?];
        while self.eat(false, Token::Comma).is_some() {
            list.push(func(self, true)?);
        }
        Some(list)
        // })
    }

    // exp := <value>
    //      | <unop> <exp>
    //      | <exp> <binop> <exp> ;;
    fn p_exp(&mut self, expect: bool) -> Option<Expr> {
        dbg_wrap!(self, "p_exp", || {
            let lhs = self.p_exp_primary(expect)?;
            self.p_exp_r(lhs, 0)
        })
    }

    fn p_exp_r(&mut self, lhs: Expr, min_prec: usize) -> Option<Expr> {
        dbg_wrap!(self, "p_exp_r", || {
            let mut lhs = lhs;
            // Every iteration of this loop associates to the left
            loop {
                match self.next().and_then(|tok| binop_token(&tok.ty)) {
                    // While the current token is a binary operator with a precedence that is greater than the current
                    // precedence,
                    Some(op) if op.precedence() >= min_prec => {
                        self.bump();
                        let mut rhs = self.p_exp_primary(true)?;

                        // Every iteration of this loop associates to the right. With `A + B * C`, `B * C` gets
                        // grouped into a single expression, leaving `A + E`, which then gets grouped into an
                        // expression by the lhs assignment.
                        loop {
                            match self.next().and_then(|tok| binop_token(&tok.ty)) {
                                Some(nop)
                                    if nop.precedence() > op.precedence()
                                        || (nop.precedence() == op.precedence()
                                            && nop.is_right_assoc()) =>
                                {
                                    // Group everything with a greater precedence
                                    rhs = self.p_exp_r(rhs, nop.precedence())?;
                                }
                                _ => break,
                            }
                        }

                        lhs = Expr::BinOp(Box::new(lhs), op, Box::new(rhs))
                    }
                    _ => break,
                }
            }

            Some(lhs)
        })
    }

    fn p_exp_primary(&mut self, expect: bool) -> Option<Expr> {
        dbg_wrap!(
            self,
            "p_exp_primary",
            || if let Some(unop) = self.p_unop() {
                Some(Expr::UnOp(unop, Box::new(self.p_exp_primary(true)?)))
            } else {
                self.p_value(expect)
            }
        )
    }

    // value = literal | '...' | function | table-cons | function-call | var | '(' expr ')' ;
    fn p_value(&mut self, expect: bool) -> Option<Expr> {
        dbg_wrap!(self, "p_value", || Some(match self.next()?.ty {
            Token::DotDotDot => {
                self.bump();
                Expr::Varargs
            }
            Token::Kw(Keyword::Nil) => {
                self.bump();
                Expr::Nil
            }
            Token::Kw(Keyword::True) => {
                self.bump();
                Expr::True
            }
            Token::Kw(Keyword::False) => {
                self.bump();
                Expr::False
            }
            Token::Kw(Keyword::Function) => {
                self.bump();
                Expr::Func(self.p_funcbody(true)?)
            }
            Token::String(_) | Token::LongString(_) => Expr::String(self.p_string(true)?),
            Token::Number => {
                let expr = Expr::Number(parse_number(self.get_text()?)?);
                self.bump();
                expr
            }
            Token::OpenBrace => Expr::Table(self.p_tableconstructor(true)?),
            Token::OpenParen => {
                self.bump();
                let expr = self.p_exp(true)?;
                self.eat(true, Token::CloseParen)?;
                Expr::Paren(Box::new(expr))
            }
            _ => self.p_non_literal(expect)?,
        }))
    }

    // *** Abandon all hope ye who enter ***

    // non-literal = prefix suffix* ;
    fn p_non_literal(&mut self, expect: bool) -> Option<Expr> {
        dbg_wrap!(self, "p_non_literal", || {
            let start = self.p_prefix(expect)?;
            self.p_non_literal_suffix(start)
        })
    }

    fn p_non_literal_suffix(&mut self, prev: Expr) -> Option<Expr> {
        dbg_wrap!(
            self,
            "p_non_literal_suffix",
            || match self.p_suffix(prev)? {
                Ok(expr) => self.p_non_literal_suffix(expr),
                Err(expr) => Some(expr),
            }
        )
    }

    fn p_prefix(&mut self, expect: bool) -> Option<Expr> {
        dbg_wrap!(self, "p_prefix", || match self.next()?.ty {
            Token::Ident => {
                let id = self.eat_ident(true)?.into();
                Some(Expr::Lhs(Lhs::Ident(id)))
            }
            Token::OpenParen => {
                self.bump();
                let exp = self.p_exp(true)?;
                self.eat(true, Token::CloseParen)?;
                Some(Expr::Paren(Box::new(exp)))
            }
            _ => {
                if expect {
                    self.tok_err("expected start of expression", vec![]);
                }
                None
            }
        })
    }

    // returns Ok(new expr) or Err(old expr)
    fn p_suffix(&mut self, prev: Expr) -> Option<Result<Expr, Expr>> {
        dbg_wrap!(self, "p_suffix", || match self.next().map(|t| t.ty) {
            Some(Token::Dot) | Some(Token::OpenBracket) => {
                let index_expr = self.p_index()?;
                Some(Ok(Expr::Lhs(Lhs::Index(
                    Box::new(prev),
                    Box::new(index_expr),
                ))))
            }
            _ if self.can_start_call() => {
                let (method_name, params) = self.p_call(true)?;
                Some(Ok(Expr::Call(match method_name {
                    Some(name) => Call::Method(Box::new(prev), name, params),
                    None => Call::Function(Box::new(prev), params),
                })))
            }
            _ => Some(Err(prev)),
        })
    }

    // call = args | ':' :ident args ;
    fn p_call(&mut self, expect: bool) -> Option<(Option<Name>, List<Expr>)> {
        dbg_wrap!(self, "p_call", || {
            let method_call = if self.eat(false, Token::Colon).is_some() {
                Some(self.eat_ident(true)?.into())
            } else {
                None
            };

            let args = self.p_args(expect || method_call.is_some())?;
            Some((method_call, args))
        })
    }

    // index = '[' exp ']' | '.' :ident ;
    fn p_index(&mut self) -> Option<Expr> {
        dbg_wrap!(self, "p_index", || Some(match self.next()?.ty {
            Token::Dot => {
                self.bump();
                Expr::String(self.eat_ident(true)?.into())
            }
            Token::OpenBracket => {
                self.bump();
                let expr = self.p_exp(true)?;
                self.eat(true, Token::CloseBracket)?;
                expr
            }
            _ => unimplemented!(),
        }))
    }

    fn p_var(&mut self, expect: bool) -> Option<Lhs> {
        dbg_wrap!(self, "p_var", || {
            match self.p_non_literal(expect)? {
                Expr::Lhs(lhs) => Some(lhs),
                _ => {
                    // TODO: Error message
                    unimplemented!();
                    None
                }
            }
        })
    }

    // value   = literal | '...' | function | table-cons | fn-call | var | '(' expr ')' ;
    // expr    = unop expr | value (binop expr)? ;
    // prefix  = '(' expr ')' | :ident ;
    // suffix  = call | index ;
    // index   = '[' exp ']' | '.' :ident ;
    // call    = args | ':' :ident args ;
    //
    // var     = prefix suffix* index | :ident ;
    // fn-call = prefix suffix* call ;

    // functioncall := <prefixexp> <args>
    //               | <prefixexp> ":" :name <args> ;;
    fn p_functioncall(&mut self, expect: bool) -> Option<Call> {
        dbg_wrap!(self, "p_functioncall", || {
            match self.p_non_literal(expect)? {
                Expr::Call(call) => Some(call),
                _ => {
                    // TODO: Error message
                    unimplemented!();
                    None
                }
            }
        })
    }

    fn can_start_call(&self) -> bool {
        match self.next().map(|t| t.ty) {
            Some(Token::OpenParen)
            | Some(Token::Colon)
            | Some(Token::OpenBrace)
            | Some(Token::LongString(_))
            | Some(Token::String(_)) => true,
            _ => false,
        }
    }

    // args := "(" <explist>? ")" | <tableconstructor> | :string ;;
    fn p_args(&mut self, expect: bool) -> Option<List<Expr>> {
        dbg_wrap!(
            self,
            "p_args",
            || if self.eat(false, Token::OpenParen).is_some() {
                Some(if self.eat(false, Token::CloseParen).is_some() {
                    vec![]
                } else {
                    let exprs = self.p_explist(true)?;
                    self.eat(true, Token::CloseParen)?;
                    exprs
                })
            } else if let Some(s) = self.p_string(false) {
                Some(vec![Expr::String(s)])
            } else {
                Some(vec![Expr::Table(self.p_tableconstructor(true)?)])
            }
        )
    }

    // funcbody := "(" <parlist>? ")" <block> "end" ;;
    fn p_funcbody(&mut self, expect: bool) -> Option<Func> {
        dbg_wrap!(self, "p_funcbody", || {
            self.eat(expect, Token::OpenParen)?;
            let (params, varadic) = if self.eat(false, Token::CloseParen).is_some() {
                (vec![], false)
            } else {
                let ret = self.p_parlist(true)?;
                self.eat(true, Token::CloseParen)?;
                ret
            };
            let body = self.p_block();
            self.eat(true, Token::Kw(Keyword::End))?;
            Some(Func {
                params,
                body,
                varadic,
            })
        })
    }

    /// Consume input
    fn try_recover_to_parlist_close(&mut self) {
        let mut offset = 0;

        while let Some(tok) = self.lookahead(offset) {
            if tok.ty == Token::CloseParen {
                self.consume(offset);
                return;
            }
            offset += 1;
        }
    }

    // parlist := <namelist> ("," "...")? | "..." ;;
    // NOTE: we treat this production as follows here, because we want better error reporting of stray varargs.
    // parlist := (<par-item> ",") ;;
    // par-item := :ident | "..." ;;
    // If we encounter any "..." that's not at the end of the parlist, we emit an error.
    fn p_parlist(&mut self, expect: bool) -> Option<(List<Name>, bool)> {
        dbg_wrap!(self, "p_parlist", || {
            let mut err_spans = vec![];
            // List of parameter names
            let mut names = vec![];
            let mut varadic = false;

            // Eat the first `par-item`
            match self.next().map(|t| t.ty) {
                // All is normal, push the result to the list of names
                Some(Token::Ident) => names.push(self.eat_ident(true)?.into()),
                // We have a varadic function, add the span to the error list if it's not at the end
                Some(Token::DotDotDot) => {
                    varadic = true;
                    let span = self.next().unwrap().span;
                    self.bump();
                    if self.check(Token::Comma) {
                        err_spans.push(span);
                    }
                }
                // wtf, just skip everything to the end of the par list
                _ => self.try_recover_to_parlist_close(),
            }

            // Eat a comma and a `par-item`
            while self.eat(false, Token::Comma).is_some() {
                let tok_span = self.next().map(|t| t.span);
                if self.eat(false, Token::DotDotDot).is_some() {
                    varadic = true;
                    // Check if we're at the end of the list by checking if the next token is a comma. If it's not at
                    // the end, add an error.
                    if self.check(Token::Comma) {
                        err_spans.push(tok_span.unwrap());
                    }
                } else {
                    // Otherwise, we should have a normal parameter
                    if let Some(ident) = self.eat_ident(true) {
                        names.push(ident.into());
                    } else {
                        // If we don't, scan to the end of the par list and return.
                        self.try_recover_to_parlist_close();
                        break;
                    }
                }
            }

            // Emit errors
            for span in err_spans {
                self.span_err(
                    span,
                    "unexpected `...`",
                    vec!["Only varargs that come at the end of a parameter list are valid.".into()],
                );
            }

            Some((names, varadic))
        })
    }

    // tableconstructor := "{" <fieldlist>? "}" ;;
    fn p_tableconstructor(&mut self, expect: bool) -> Option<List<TableEntry>> {
        dbg_wrap!(self, "p_tableconstructor", || {
            self.eat(expect, Token::OpenBrace)?;
            if self.eat(false, Token::CloseBrace).is_some() {
                Some(vec![])
            } else {
                let list = self.p_fieldlist(true)?;
                self.eat(true, Token::CloseBrace)?;
                Some(list)
            }
        })
    }

    // fieldlist := <field> (<fieldsep> <field>)* <fieldsep>? ;;
    fn p_fieldlist(&mut self, expect: bool) -> Option<List<TableEntry>> {
        dbg_wrap!(self, "p_fieldlist", || {
            let mut cur_idx = 1;

            let (was_bare_expr, field) = self.p_field(expect, cur_idx)?;
            cur_idx += was_bare_expr as usize;
            let mut fields = vec![field];
            while self.p_fieldsep().is_some() {
                let (was_bare_expr, field) = self.p_field(true, cur_idx)?;
                cur_idx += was_bare_expr as usize;
                fields.push(field);
            }

            let _ = self.p_fieldsep();
            Some(fields)
        })
    }

    // field := "[" <exp> "]" "=" <exp> | :name "=" <exp> | <exp> ;;
    fn p_field(&mut self, expect: bool, cur_idx: usize) -> Option<(bool, TableEntry)> {
        dbg_wrap!(
            self,
            "p_field",
            || if self.eat(false, Token::OpenBracket).is_some() {
                let key = self.p_exp(true)?;
                self.eat(true, Token::CloseBracket)?;
                self.eat(true, Token::Eq)?;
                let val = self.p_exp(true)?;
                Some((false, TableEntry { key, val }))
            } else if let Some(key) = self.eat_ident(false) {
                self.eat(true, Token::Eq)?;
                let val = self.p_exp(true)?;
                Some((
                    false,
                    (TableEntry {
                        key: Expr::String(key.into()),
                        val,
                    }),
                ))
            } else {
                Some((
                    true,
                    TableEntry {
                        key: Expr::Number(cur_idx as f64),
                        val: self.p_exp(expect)?,
                    },
                ))
            }
        )
    }

    // fieldsep := "," | ";" ;;
    fn p_fieldsep(&mut self) -> Option<()> {
        dbg_wrap!(
            self,
            "p_fieldsep",
            || if self.eat(false, Token::Comma).is_some() {
                return Some(());
            } else {
                self.eat(false, Token::Semicolon)?;
                Some(())
            }
        )
    }

    // binop :=
    //   "+" |  "-" |  "*" |  "/" | "//" |  "^" | "%" |
    // 	 "&" |  "~" |  "|" | ">>" | "<<" | ".." |
    // 	 "<" | "<=" |  ">" | ">=" | "==" | "~=" |
    // 	 "and" | "or" ;;
    fn p_binop(&mut self) -> Option<BinOp> {
        dbg_wrap!(self, "p_binop", || {
            let op = binop_token(&self.next()?.ty);
            if op.is_some() {
                self.bump();
            }
            op
        })
    }

    // unop := "-" | "not" | "#" | "~" ;;
    fn p_unop(&mut self) -> Option<UnOp> {
        dbg_wrap!(self, "p_unop", || {
            let op = unop_token(&self.next()?.ty);
            if op.is_some() {
                self.bump();
            }
            op
        })
    }

    fn p_string(&mut self, expect: bool) -> Option<String> {
        dbg_wrap!(self, "p_string", || {
            let tok = self.next()?;
            Some(match tok.ty {
                Token::String(_) => {
                    self.bump();
                    StringParser::parse(self, 1, *tok)
                }
                Token::LongString(n) => {
                    self.bump();
                    StringParser::parse(self, n, *tok)
                }
                _ => {
                    if expect {
                        self.tok_err(
                            "expected string literal",
                            vec![format!(
                                "I was looking for a string but I found `{:?}` instead",
                                tok.ty
                            )],
                        );
                    }
                    return None;
                }
            })
        })
    }
}

fn unop_token(tok: &Token) -> Option<UnOp> {
    Some(match tok {
        Token::Minus => UnOp::Minus,
        Token::Kw(Keyword::Not) => UnOp::Not,
        Token::Hash => UnOp::Length,
        Token::Tilde => UnOp::BitNot,

        _ => return None,
    })
}

fn binop_token(tok: &Token) -> Option<BinOp> {
    Some(match tok {
        Token::Plus => BinOp::Add,
        Token::Minus => BinOp::Sub,
        Token::Star => BinOp::Mul,
        Token::Slash => BinOp::Div,
        Token::ShashSlash => BinOp::FloorDiv,
        Token::Exp => BinOp::Exp,
        Token::Percent => BinOp::Mod,

        Token::BitAnd => BinOp::BitAnd,
        Token::Tilde => BinOp::BitXor,
        Token::BitOr => BinOp::BitOr,
        Token::GtGt => BinOp::BitShr,
        Token::LtLt => BinOp::BitShl,
        Token::DotDot => BinOp::Concat,

        Token::Lt => BinOp::Less,
        Token::LtEq => BinOp::LessEq,
        Token::Gt => BinOp::Greater,
        Token::GtEq => BinOp::GreaterEq,
        Token::EqEq => BinOp::Eq,
        Token::TildeEq => BinOp::NotEq,

        Token::Kw(Keyword::And) => BinOp::And,
        Token::Kw(Keyword::Or) => BinOp::Or,

        // TODO: error reporting
        _ => return None,
    })
}

struct StringParser<'src, 'ctx> {
    src: &'src str,
    remaining: usize,
    idx: Index,
    char_start: Index,
    buf: String,
    errs: &'ctx mut ErrorManager,
}

impl<'src, 'ctx> StringParser<'src, 'ctx> {
    fn parse(p: &mut Parser<'src, 'ctx>, delim_len: usize, tok: SpannedToken) -> String {
        let span = tok.span.shrink_n_same_line(delim_len);
        let len = span.byte_len();
        let mut p = StringParser {
            src: p.src,
            remaining: len,
            idx: span.start,
            char_start: span.start,
            buf: String::with_capacity(len),
            errs: p.errs,
        };
        p.p_short_string();
        p.buf
    }
}

impl<'src> StringParser<'src, '_> {
    fn get_ch(&mut self) -> char {
        self.remaining -= 1;
        let ch = self.src[self.idx.byte..].chars().next().unwrap();
        self.idx = self.idx.advance_by(ch);
        ch
    }

    fn peek_ch(&self, offset: usize) -> char {
        self.src[self.idx.byte + offset..].chars().next().unwrap()
    }

    fn get_str(&mut self, len: usize) -> &'src str {
        let s = &self.src[self.idx.byte..self.idx.byte + len];
        for ch in s.chars() {
            self.remaining -= 1;
            self.idx = self.idx.advance_by(ch);
        }
        s
    }

    fn escape_hex(&mut self) {
        let codepoint = u32::from_str_radix(self.get_str(2), 16).unwrap();
        match std::char::from_u32(codepoint) {
            Some(ch) => self.buf.push(ch),
            None => self.errs.span_error(
                Span::new(self.char_start, self.idx)
                    .error_diagnostic()
                    .with_message("invalid codepoint")
                    .with_annotation(Level::Note, format!("I was looking for a valid codepoint but I found a codepoint with the value of `{}`.", codepoint)),
            ),
        }
    }

    fn expect(&mut self, ch: char) {
        let next = self.get_ch();
        if next != ch {
            self.errs.span_error(
                Span::new(self.idx, self.idx.advance_by(next))
                    .error_diagnostic()
                    .with_message("unexpected character")
                    .with_annotation(
                        Level::Note,
                        format!("I was looking for `{}`, but I found `{}` :c", ch, next),
                    ),
            )
        }
    }

    fn escape_unicode(&mut self) {
        self.expect('{');
        let start = self.idx;
        let mut len = 0;
        while self.peek_ch(len).is_digit(16) {
            len += 1;
        }
        let s = self.get_str(len);
        let ch = match u32::from_str_radix(s, 16)
            .ok()
            .and_then(|num| std::char::from_u32(num))
        {
            Some(num) => num,
            None => {
                self.errs.span_error(
                    Span::new(start, self.idx)
                        .error_diagnostic()
                        .with_message("invalid codepoint"),
                );
                return;
            }
        };
        self.buf.push(ch);
        self.expect('}');
    }

    fn escape_code(&mut self, code: char) {
        match code {
            'a' => self.buf.push('\x07'),
            'b' => self.buf.push('\x08'),
            't' => self.buf.push('\x09'),
            'n' => self.buf.push('\x0A'),
            'v' => self.buf.push('\x0B'),
            'f' => self.buf.push('\x0C'),
            'r' => self.buf.push('\x0D'),
            '\\' => self.buf.push('\\'),
            '"' => self.buf.push('"'),
            '\'' => self.buf.push('\''),
            '\n' => self.buf.push('\n'),
            'x' => self.escape_hex(),
            'u' => self.escape_unicode(),
            _ => panic!("lexer allowed invalid escape code"),
        }
    }

    fn p_short_string(&mut self) {
        while self.remaining > 0 {
            self.char_start = self.idx;
            match self.get_ch() {
                '\\' => {
                    let ch = self.get_ch();
                    self.escape_code(ch)
                }
                ch => self.buf.push(ch),
            }
        }

        self.buf.shrink_to_fit();
    }
}

fn parse_number(src: &str) -> Option<f64> {
    // let mut num = 0.0;
    // let (start, radix, pow_ch) = if src.starts_with("0x") || src.starts_with("0X") {
    //     (2, 16, 'p')
    // } else {
    //     (0, 10, 'e')
    // };

    // let whole_len = src[start..].chars().take_while(|&ch| ch != '.').count();
    // let dec_start = start + whole_len + 1;
    // let dec_len = src[dec_start..].chars().take_while(|&ch| ch != '.').count();

    // let whole = &src[start..start + whole_len];
    // let decimal = &src[dec_start..dec_start + dec_len];

    // unimplemented!()
    src.parse().ok()
}
