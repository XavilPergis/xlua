use xlua::error::ErrorManager;
use xlua::parse::*;
use xlua::token::Tokenizer;

fn print_unop(op: UnOp) {
    print!(
        "{}",
        match op {
            UnOp::Minus => "-",
            UnOp::Not => "not",
            UnOp::Length => "#",
            UnOp::BitNot => "~",
        }
    )
}

fn print_op(op: BinOp) {
    print!(
        "{}",
        match op {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::FloorDiv => "//",
            BinOp::Exp => "^",
            BinOp::Mod => "%",
            BinOp::BitAnd => "&",
            BinOp::BitXor => "~",
            BinOp::BitOr => "|",
            BinOp::BitShr => ">>",
            BinOp::BitShl => "<<",
            BinOp::Concat => "..",
            BinOp::Less => "<",
            BinOp::LessEq => "<=",
            BinOp::Greater => ">",
            BinOp::GreaterEq => ">=",
            BinOp::Eq => "==",
            BinOp::NotEq => "~=",
            BinOp::And => "and",
            BinOp::Or => "or",
        }
    )
}

fn print_lhs(lhs: &Lhs) {
    match lhs {
        Lhs::Ident(name) => print!("{}", name),
        Lhs::Index(expr, idx) => {
            print_expr(expr);
            print!("[");
            print_expr(idx);
            print!("]");
        }
    }
}

fn print_expr(expr: &Expr) {
    match expr {
        Expr::Nil => print!("nil"),
        Expr::True => print!("true"),
        Expr::False => print!("false"),
        Expr::Varargs => print!("..."),
        Expr::Number(k) => print!("{}", k),
        Expr::String(s) => print!("\"{}\"", s),
        Expr::Func(f) => {
            print!("function(");
            print_list(&f.params, |n| print!("{}", n));
            print!(") ... end");
        }
        Expr::Table(entries) => print!("{{ ... }}"),
        Expr::BinOp(lhs, op, rhs) => {
            print!("(");
            print_expr(lhs);
            print!(") ");
            print_op(*op);
            print!(" (");
            print_expr(rhs);
            print!(")");
        }
        Expr::UnOp(op, operand) => {
            print_unop(*op);
            print!("(");
            print_expr(operand);
            print!(")");
        }
        Expr::Paren(expr) => {
            print!("(");
            print_expr(&expr);
            print!(")");
        }

        Expr::Lhs(lhs) => print_lhs(lhs),
        Expr::Call(call) => match call {
            Call::Function(func, args) => {
                print_expr(func);
                print!("(");
                print_list(args, print_expr);
                print!(")");
            }
            Call::Method(obj, name, args) => {
                print_expr(obj);
                print!(":{}(", name);
                print_list(args, print_expr);
                print!(")");
            }
        },
    }
}

fn print_list<T, F>(list: &[T], func: F)
where
    F: Fn(&T),
{
    let mut iter = list.iter();
    if let Some(first) = iter.next() {
        func(first);
    }
    for expr in iter {
        print!(", ");
        func(expr);
    }
}

fn main() {
    let file = std::env::args().skip(1).next().unwrap();
    let contents = std::fs::read(&file).unwrap();
    let contents = String::from_utf8(contents).unwrap();

    let mut tokens = vec![];
    let mut err_ctx = ErrorManager::new();

    {
        let mut tokenizer = Tokenizer::new(&contents, &mut err_ctx);

        while let Some(tok) = tokenizer.scan() {
            // println!(
            //     "{:?} / {}",
            //     tok.ty,
            //     &contents[tok.span.start.byte..tok.span.end.byte]
            // );

            tokens.push(tok);
        }
    }

    if err_ctx.has_errors() {
        err_ctx.emit(&contents);
        return;
    }
    println!();

    {
        let mut parser = Parser::new(&contents, &tokens, &mut err_ctx);
        let ast = parser.p_chunk();
        println!();
        println!("{:#?}", ast);
        for stmt in &ast.unwrap().statements {
            match stmt {
                Statement::Assign(names, exprs) => {
                    print_list(names, print_lhs);
                    print!(" = ");
                    print_list(exprs, print_expr);
                }
                _ => print!("<stmt>"),
            }
        }
        println!();
    }

    err_ctx.emit(&contents);
}
