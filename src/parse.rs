use crate::error::ErrorManager;
use crate::error::Level;
use crate::span::Index;
use crate::span::Span;
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
    StringLiteral(String),

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

struct ParseFail {}

type PResult<T> = Result<T, ParseFail>;

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
            print!("| ");
        }
    }

    fn check(&self, tok: Token) -> bool {
        self.idx < self.tokens.len() && self.tokens[self.idx].ty == tok
    }

    fn check_lookahead(&self, lookahead: usize, tok: Token) -> bool {
        self.idx + lookahead < self.tokens.len() && self.tokens[self.idx + lookahead].ty == tok
    }

    fn eat(&mut self, tok: Token) -> Option<()> {
        if self.check(tok) {
            self.bump();
            Some(())
        } else {
            None
        }
    }

    fn get_text(&self) -> Option<&'src str> {
        let span = self.next()?.span;
        Some(&self.src[span.start.byte..span.end.byte])
    }

    fn expect_err<T: std::fmt::Debug>(&mut self, item: T) {
        self.dbg_pad();
        println!("@! bad expect {:?} / {:?}", item, self.next().map(|t| t.ty));
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

    fn expect(&mut self, tok: Token) -> Option<()> {
        if self.eat(tok).is_some() {
            Some(())
        } else {
            self.expect_err(tok);
            None
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
        println!("@ bumped {:?}", self.tokens[self.idx].ty);
        self.idx += 1;
    }

    fn eat_ident(&mut self) -> Option<&'src str> {
        if self.check(Token::Ident) {
            let span = self.next()?.span;
            self.bump();
            Some(&self.src[span.start.byte..span.end.byte])
        } else {
            None
        }
    }

    fn expect_ident(&mut self) -> Option<&'src str> {
        if self.check(Token::Ident) {
            let span = self.next()?.span;
            self.bump();
            Some(&self.src[span.start.byte..span.end.byte])
        } else {
            self.expect_err("ident");
            None
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
        $self.dbg_pad();
        println!("< {:?}", ret);
        // $self.dbg_pad();
        // println!("+<-- {} {:?}", $name, ret);
        ret
    }};
}

impl Parser<'_, '_> {
    // chunk := <block> ;;
    pub fn p_chunk(&mut self) -> Option<Block> {
        dbg_wrap!(self, "p_chunk", || self.p_block())
    }

    // block := <stat>* <retstat>? ;;
    fn p_block(&mut self) -> Option<Block> {
        dbg_wrap!(self, "p_block", || {
            let mut statements = vec![];
            while let Some(stmt) = self.p_stat() {
                statements.push(stmt);
            }
            let return_statement = self.p_retstat();

            Some(Block {
                statements,
                return_statement,
            })
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
                    if let Some(ident) = self.eat_ident() {
                        Statement::Goto(ident.into())
                    } else {
                        unimplemented!()
                    }
                }
                Token::Kw(Keyword::Do) => {
                    self.bump();
                    let block = self.p_block()?;
                    self.expect(Token::Kw(Keyword::End))?;
                    Statement::Do(block)
                }
                Token::Kw(Keyword::While) => {
                    self.bump();
                    let cond = self.p_exp()?;
                    self.expect(Token::Kw(Keyword::Do))?;
                    let block = self.p_block()?;
                    Statement::While(ExprAndBlock { cond, block })
                }
                Token::Kw(Keyword::Repeat) => {
                    self.bump();
                    let block = self.p_block()?;
                    self.expect(Token::Kw(Keyword::Until))?;
                    let cond = self.p_exp()?;
                    Statement::Repeat(ExprAndBlock { cond, block })
                }
                // The colon syntax is used for defining methods, that is, functions that have an implicit extra parameter self. Thus, the statement
                //     function t.a.b.c:f (params) body end
                // is syntactic sugar for
                //     t.a.b.c.f = function (self, params) body end
                Token::Kw(Keyword::Function) => {
                    self.bump();
                    let (lhs_path, method) = self.p_funcname()?;
                    let mut body = self.p_funcbody()?;

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
                                    Box::new(Expr::StringLiteral(idx)),
                                )
                            }
                        }
                    }

                    let lhs = path_to_lhs(lhs_path);
                    let lhs = if let Some(ident) = method {
                        Lhs::Index(
                            Box::new(Expr::Lhs(lhs)),
                            Box::new(Expr::StringLiteral(ident)),
                        )
                    } else {
                        lhs
                    };

                    Statement::Assign(vec![lhs], vec![Expr::Func(body)])
                }
                Token::Kw(Keyword::Local) => {
                    self.bump();
                    if self.eat(Token::Kw(Keyword::Function)).is_some() {
                        let ident = self.eat_ident()?.into();
                        let body = self.p_funcbody()?;
                        Statement::LocalFunc(ident, body)
                    } else {
                        let names = self.p_namelist()?;
                        let vals = if self.eat(Token::Eq).is_some() {
                            Some(self.p_explist()?)
                        } else {
                            None
                        };
                        Statement::Local(names, vals)
                    }
                }
                Token::ColonColon => Statement::Label(self.p_label()?),
                Token::Kw(Keyword::If) => Statement::If(self.p_if_stat()?),
                Token::Kw(Keyword::For) => Statement::For(self.p_for_stat()?),

                Token::Ident => {
                    // starts with an ident so it's either an assignment or a function call...
                    // if we are looking at a var list, then we have `[ident] "," ...` or `[ident] "=" ...`
                    // otherwise, we probably have a function call.
                    if self.check_lookahead(1, Token::Comma) || self.check_lookahead(1, Token::Eq) {
                        let vars = self.p_varlist()?;
                        self.expect(Token::Eq)?;
                        let exprs = self.p_explist()?;
                        Statement::Assign(vars, exprs)
                    } else {
                        Statement::Call(self.p_functioncall()?)
                    }
                }

                _ => return None,
            })
        })
    }

    // if_stmt  := "if" <exp> "then" <block> ("elseif" <exp> "then" <block>)* ("else" <block>)? "end" ;;
    fn p_if_stat(&mut self) -> Option<If> {
        dbg_wrap!(self, "p_if_stat", || {
            self.eat(Token::Kw(Keyword::If))?;
            let cond = self.p_exp()?;
            self.expect(Token::Kw(Keyword::Then))?;
            let block = self.p_block()?;
            let if_clause = ExprAndBlock { cond, block };

            let mut elseif_clauses = vec![];
            while self.eat(Token::Kw(Keyword::ElseIf)).is_some() {
                let cond = self.p_exp()?;
                self.expect(Token::Kw(Keyword::Then))?;
                let block = self.p_block()?;
                elseif_clauses.push(ExprAndBlock { cond, block })
            }

            let else_clause = if self.eat(Token::Kw(Keyword::Else)).is_some() {
                Some(self.p_block()?)
            } else {
                None
            };

            Some(If {
                if_clause,
                elseif_clauses,
                else_clause,
            })
        })
    }

    // for_stmt := "for" :name "=" <exp> "," <exp> ("," <exp>)? "do" <block> "end"
    // 	         | "for" <namelist> "in" <explist> "do" <block> "end" ;;
    fn p_for_stat(&mut self) -> Option<For> {
        dbg_wrap!(self, "p_for_stat", || {
            self.eat(Token::Kw(Keyword::For))?;
            Some(if self.check_lookahead(1, Token::Eq) {
                println!("numeric for");
                // numerical for loop
                let binding = self.eat_ident()?.into();
                println!("foo {:?}", binding);
                self.expect(Token::Eq)?;
                println!("bar");
                let start = self.p_exp()?;
                self.expect(Token::Comma)?;
                let end = self.p_exp()?;
                let step = if self.eat(Token::Comma).is_some() {
                    Some(self.p_exp()?)
                } else {
                    None
                };
                self.expect(Token::Kw(Keyword::Do))?;
                let block = self.p_block()?;
                self.expect(Token::Kw(Keyword::End))?;

                For::Numeric {
                    binding,
                    start,
                    end,
                    step,
                    block,
                }
            } else {
                println!("generic for");
                let bindings = self.p_namelist()?;
                self.expect(Token::Kw(Keyword::In))?;
                let iterators = self.p_explist()?;
                self.expect(Token::Kw(Keyword::Do))?;
                let block = self.p_block()?;
                self.expect(Token::Kw(Keyword::End))?;
                For::Generic {
                    bindings,
                    iterators,
                    block,
                }
            })
        })
    }

    // retstat := "return" <explist>? ";"? ;;
    fn p_retstat(&mut self) -> Option<List<Expr>> {
        dbg_wrap!(self, "p_retstat", || {
            self.eat(Token::Kw(Keyword::Return))?;
            let exprs = self.p_explist()?;
            let _ = self.eat(Token::Semicolon);
            Some(exprs)
        })
    }

    // label := "::" :name "::" ;;
    fn p_label(&mut self) -> Option<Name> {
        dbg_wrap!(self, "p_label", || {
            self.eat(Token::ColonColon)?;
            let name = self.eat_ident()?;
            self.expect(Token::ColonColon)?;
            Some(name.into())
        })
    }

    // funcname := :name ("." :name)* (":" :name)? ;;
    fn p_funcname(&mut self) -> Option<(List<Name>, Option<Name>)> {
        dbg_wrap!(self, "p_funcname", || {
            let mut path = vec![self.eat_ident()?.into()];

            while self.eat(Token::Dot).is_some() {
                path.push(self.eat_ident()?.into());
            }

            let method = if self.eat(Token::Colon).is_some() {
                Some(self.eat_ident()?.into())
            } else {
                None
            };

            Some((path, method))
        })
    }

    // varlist := <var> ("," <var>)* ;;
    fn p_varlist(&mut self) -> Option<List<Lhs>> {
        dbg_wrap!(self, "p_varlist", || self.p_list_generic(|p| p.p_var()))
    }

    // namelist := :name ("," :name)* ;;
    fn p_namelist(&mut self) -> Option<List<Name>> {
        dbg_wrap!(self, "p_namelist", || self
            .p_list_generic(|p| p.eat_ident().map(Into::into)))
    }

    // explist := <exp> ("," <exp>)* ;;
    fn p_explist(&mut self) -> Option<List<Expr>> {
        dbg_wrap!(self, "p_explist", || self.p_list_generic(|p| p.p_exp()))
    }

    fn p_list_generic<T, F>(&mut self, mut func: F) -> Option<List<T>>
    where
        F: FnMut(&mut Self) -> Option<T>,
    {
        // dbg_wrap!(self, "p_for_stat", || {
        let mut list = vec![func(self)?];
        while self.eat(Token::Comma).is_some() {
            list.push(func(self)?);
        }
        Some(list)
        // })
    }

    // exp := <value>
    //      | <unop> <exp>
    //      | <exp> <binop> <exp> ;;
    fn p_exp(&mut self) -> Option<Expr> {
        dbg_wrap!(self, "p_exp", || {
            let lhs = self.p_exp_primary()?;
            self.p_exp_r(lhs, 0)
        })
    }

    fn p_exp_r(&mut self, lhs: Expr, min_prec: usize) -> Option<Expr> {
        dbg_wrap!(self, "p_exp_r", || {
            let mut lhs = lhs;
            loop {
                match self.next().and_then(|tok| binop_token(&tok.ty)) {
                    Some(op) if binop_prec(op) >= min_prec => {
                        self.bump();
                        let mut rhs = self.p_exp_primary()?;

                        loop {
                            match self.next().and_then(|tok| binop_token(&tok.ty)) {
                                Some(nop) if binop_prec(nop) > binop_prec(op) => {
                                    rhs = self.p_exp_r(rhs, binop_prec(nop))?
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

    // NOTE: `<unop> <primary>` do that `-a + b` is `((-a) + (b))` and not `(-((a) + (b)))` like you'd get with `<unop> <exp>`
    // exp-primary := <value> | <unop> <exp-primary> ;;
    fn p_exp_primary(&mut self) -> Option<Expr> {
        dbg_wrap!(
            self,
            "p_exp_primary",
            || if let Some(unop) = self.p_unop() {
                Some(Expr::UnOp(unop, Box::new(self.p_exp_primary()?)))
            } else {
                self.p_value()
            }
        )
    }

    // value = literal | '...' | function | table-cons | function-call | var | '(' expr ')' ;
    fn p_value(&mut self) -> Option<Expr> {
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
                Expr::Func(self.p_funcbody()?)
            }
            Token::LongString | Token::SingleQuoteString | Token::DoubleQuoteString => {
                Expr::StringLiteral(self.p_string()?)
            }
            Token::Float | Token::Int => {
                let expr = Expr::Number(parse_number(self.get_text()?)?);
                self.bump();
                expr
            }
            Token::OpenBrace => Expr::Table(self.p_tableconstructor()?),
            Token::OpenParen => {
                self.bump();
                let expr = self.p_exp()?;
                self.expect(Token::CloseParen)?;
                Expr::Paren(Box::new(expr))
            }
            _ => self.p_non_literal()?,
        }))
    }

    // *** Abandon all hope ye who enter ***

    // non-literal = prefix suffix* ;
    fn p_non_literal(&mut self) -> Option<Expr> {
        dbg_wrap!(self, "p_non_literal", || {
            let start = self.p_prefix()?;
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

    fn p_prefix(&mut self) -> Option<Expr> {
        dbg_wrap!(self, "p_prefix", || match self.next()?.ty {
            Token::Ident => {
                let id = self.eat_ident()?.into();
                Some(Expr::Lhs(Lhs::Ident(id)))
            }
            Token::OpenParen => {
                self.bump();
                let exp = self.p_exp()?;
                self.expect(Token::CloseParen)?;
                Some(Expr::Paren(Box::new(exp)))
            }
            _ => unimplemented!(),
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
                let (method_name, params) = self.p_call()?;
                Some(Ok(Expr::Call(match method_name {
                    Some(name) => Call::Method(Box::new(prev), name, params),
                    None => Call::Function(Box::new(prev), params),
                })))
            }
            _ => Some(Err(prev)),
        })
    }

    // call = args | ':' :ident args ;
    fn p_call(&mut self) -> Option<(Option<Name>, List<Expr>)> {
        dbg_wrap!(self, "p_call", || {
            let method_call = if self.eat(Token::Colon).is_some() {
                Some(self.expect_ident()?.into())
            } else {
                None
            };

            let args = self.p_args()?;
            Some((method_call, args))
        })
    }

    // index = '[' exp ']' | '.' :ident ;
    fn p_index(&mut self) -> Option<Expr> {
        dbg_wrap!(self, "p_index", || Some(match self.next()?.ty {
            Token::Dot => {
                self.bump();
                Expr::StringLiteral(self.eat_ident()?.into())
            }
            Token::OpenBracket => {
                self.bump();
                let expr = self.p_exp()?;
                self.expect(Token::CloseBracket)?;
                expr
            }
            _ => unimplemented!(),
        }))
    }

    fn p_var(&mut self) -> Option<Lhs> {
        dbg_wrap!(self, "p_var", || {
            match self.p_non_literal()? {
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
    fn p_functioncall(&mut self) -> Option<Call> {
        dbg_wrap!(self, "p_functioncall", || {
            match self.p_non_literal()? {
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
        self.check(Token::OpenParen)
            || self.check(Token::Colon)
            || self.check(Token::OpenBracket)
            || self.check(Token::LongString)
            || self.check(Token::SingleQuoteString)
            || self.check(Token::DoubleQuoteString)
    }

    // args := "(" <explist>? ")" | <tableconstructor> | :string ;;
    fn p_args(&mut self) -> Option<List<Expr>> {
        dbg_wrap!(self, "p_args", || if self.eat(Token::OpenParen).is_some() {
            Some(if self.eat(Token::CloseParen).is_some() {
                vec![]
            } else {
                let exprs = self.p_explist()?;
                self.expect(Token::CloseParen)?;
                exprs
            })
        } else if let Some(s) = self.p_string() {
            Some(vec![Expr::StringLiteral(s)])
        } else {
            Some(vec![Expr::Table(self.p_tableconstructor()?)])
        })
    }

    // funcbody := "(" <parlist>? ")" <block> "end" ;;
    fn p_funcbody(&mut self) -> Option<Func> {
        dbg_wrap!(self, "p_funcbody", || {
            self.eat(Token::OpenParen)?;
            let (params, varadic) = if self.eat(Token::CloseParen).is_some() {
                (vec![], false)
            } else {
                let ret = self.p_parlist()?;
                self.expect(Token::CloseParen)?;
                ret
            };
            let body = self.p_block()?;
            self.expect(Token::Kw(Keyword::End))?;
            Some(Func {
                params,
                body,
                varadic,
            })
        })
    }

    // parlist := <namelist> ("," "...")? | "..." ;;
    fn p_parlist(&mut self) -> Option<(List<Name>, bool)> {
        dbg_wrap!(
            self,
            "p_parlist",
            || if self.eat(Token::DotDotDot).is_some() {
                Some((vec![], true))
            } else {
                let list = self.p_namelist()?;
                let varadic = self.eat(Token::Comma).is_some();
                if varadic {
                    self.expect(Token::DotDotDot)?;
                }
                Some((list, varadic))
            }
        )
    }

    // tableconstructor := "{" <fieldlist>? "}" ;;
    fn p_tableconstructor(&mut self) -> Option<List<TableEntry>> {
        dbg_wrap!(self, "p_tableconstructor", || {
            self.eat(Token::OpenBrace)?;
            if self.eat(Token::CloseBrace).is_some() {
                Some(vec![])
            } else {
                let list = self.p_fieldlist()?;
                self.expect(Token::CloseBrace)?;
                Some(list)
            }
        })
    }

    // fieldlist := <field> (<fieldsep> <field>)* <fieldsep>? ;;
    fn p_fieldlist(&mut self) -> Option<List<TableEntry>> {
        dbg_wrap!(self, "p_fieldlist", || {
            let mut cur_idx = 1;

            let (was_bare_expr, field) = self.p_field(cur_idx)?;
            cur_idx += was_bare_expr as usize;
            let mut fields = vec![field];
            while self.p_fieldsep().is_some() {
                let (was_bare_expr, field) = self.p_field(cur_idx)?;
                cur_idx += was_bare_expr as usize;
                fields.push(field);
            }

            let _ = self.p_fieldsep();
            Some(fields)
        })
    }

    // field := "[" <exp> "]" "=" <exp> | :name "=" <exp> | <exp> ;;
    fn p_field(&mut self, cur_idx: usize) -> Option<(bool, TableEntry)> {
        dbg_wrap!(
            self,
            "p_field",
            || if self.eat(Token::OpenBracket).is_some() {
                let key = self.p_exp()?;
                self.expect(Token::CloseBracket)?;
                self.expect(Token::Eq)?;
                let val = self.p_exp()?;
                Some((false, TableEntry { key, val }))
            } else if let Some(key) = self.eat_ident() {
                self.expect(Token::Eq)?;
                let val = self.p_exp()?;
                Some((
                    false,
                    (TableEntry {
                        key: Expr::StringLiteral(key.into()),
                        val,
                    }),
                ))
            } else {
                Some((
                    true,
                    TableEntry {
                        key: Expr::Number(cur_idx as f64),
                        val: self.p_exp()?,
                    },
                ))
            }
        )
    }

    // fieldsep := "," | ";" ;;
    fn p_fieldsep(&mut self) -> Option<()> {
        dbg_wrap!(self, "p_fieldsep", || {
            self.eat(Token::Comma)?;
            self.eat(Token::Semicolon)?;
            Some(())
        })
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

    // Some(ch) => match ch {
    //     // Normal escape sequence, sonsume it and move on.
    //     'a' | 'b' | 'f' | 'n' | 'r' | 't' | 'v' | '\\' | '"' | '\'' | '\r' | '\n' => {
    //         self.consume(1);
    //     }

    //     // Unicode escape, like `\u{CODEPOINT}`
    //     'u' => {
    //         self.consume(1);
    //         self.scan_unicode_escape(escape_start);
    //     }

    //     // Hex escape, like `\xNN`
    //     'x' => {
    //         // consume the `x`
    //         self.consume(1);
    //         self.scan_hex_escape(escape_start);
    //     }

    //     ch if ch.is_digit(10) => {
    //         self.scan_dec_escape();
    //     }

    //     ch => self.errs.span_error(
    //         Span::new(escape_start, self.idx)
    //             .error_diagnostic()
    //             .with_message("unknown escape code")
    //             .with_annotation(
    //                 Level::Note,
    //                 format!("I was looking for an escape code, but I found `{}` which is not one", ch),
    //             ),
    //     ),
    // },

    // '\a' (bell), '\b' (backspace), '\f' (form feed), '\n' (newline),
    // '\r' (carriage return), '\t' (horizontal tab), '\v' (vertical tab),
    // '\\' (backslash), '\"' (quotation mark [double quote]), and '\'' (apostrophe [single quote]).

    fn p_string(&mut self) -> Option<String> {
        dbg_wrap!(self, "p_string", || {
            let tok = self.next()?;
            self.bump();
            Some(match tok.ty {
                Token::SingleQuoteString => ShortStringParser::parse(self, '\'', *tok),
                Token::DoubleQuoteString => ShortStringParser::parse(self, '"', *tok),
                _ => unimplemented!(),
            })
        })
    }

    fn p_int(&mut self) -> Option<f64> {
        dbg_wrap!(self, "p_int", || {
            self.eat(Token::Int)?;

            unimplemented!()
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
        Token::Kw(Keyword::Or) => BinOp::And,

        // TODO: error reporting
        _ => return None,
    })
}

/// Binary operator precedence
fn binop_prec(op: BinOp) -> usize {
    match op {
        BinOp::Or => 0,
        BinOp::And => 1,

        BinOp::Less => 2,
        BinOp::LessEq => 2,
        BinOp::Greater => 2,
        BinOp::GreaterEq => 2,
        BinOp::Eq => 2,
        BinOp::NotEq => 2,

        BinOp::BitOr => 3,
        BinOp::BitXor => 4,
        BinOp::BitAnd => 5,
        BinOp::BitShr => 6,
        BinOp::BitShl => 6,
        BinOp::Concat => 7,

        BinOp::Add => 8,
        BinOp::Sub => 8,
        BinOp::Mul => 9,
        BinOp::Div => 9,
        BinOp::FloorDiv => 9,
        BinOp::Mod => 9,
        BinOp::Exp => 10,
    }
}

struct ShortStringParser<'src, 'ctx> {
    src: &'src str,
    str_delim: char,
    idx: Index,
    char_start: Index,
    buf: String,
    errs: &'ctx mut ErrorManager,
}

impl<'src, 'ctx> ShortStringParser<'src, 'ctx> {
    fn parse(p: &mut Parser<'src, 'ctx>, delim: char, tok: SpannedToken) -> String {
        let mut p = ShortStringParser {
            src: p.src,
            str_delim: delim,
            idx: tok.span.start,
            char_start: tok.span.start,
            buf: String::with_capacity(tok.span.end.byte - tok.span.start.byte),
            errs: p.errs,
        };
        p.p_short_string();
        p.buf
    }
}

impl<'src> ShortStringParser<'src, '_> {
    fn get_ch(&mut self) -> char {
        let ch = self.src[self.idx.byte..].chars().next().unwrap();
        self.idx = self.idx.advance_by(ch);
        ch
    }

    fn get_str(&mut self, len: usize) -> &'src str {
        let s = &self.src[self.idx.byte..self.idx.byte + len];
        for ch in s.chars() {
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

    fn escape_code(&mut self, code: char) {
        match code {
            'a' => self.buf.push('\x07'),
            'b' => self.buf.push('\x08'),
            'n' => self.buf.push('\x0A'),
            'f' => self.buf.push('\x0C'),
            'r' => self.buf.push('\x0D'),
            't' => self.buf.push('\x09'),
            'v' => self.buf.push('\x0B'),
            '\\' => self.buf.push('\\'),
            '"' => self.buf.push('"'),
            '\'' => self.buf.push('\''),
            'x' => {}
            _ => panic!("lexer allowed invalid escape code"),
        }
    }

    fn p_short_string(&mut self) {
        loop {
            self.char_start = self.idx;
            match self.get_ch() {
                '\\' => {
                    let ch = self.get_ch();
                    self.escape_code(ch)
                }
                ch if ch == self.str_delim => break,
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
