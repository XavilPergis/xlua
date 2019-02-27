use xlua::error::ErrorManager;
use xlua::parse::*;
use xlua::token::Tokenizer;

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
    }

    err_ctx.emit(&contents);
}
