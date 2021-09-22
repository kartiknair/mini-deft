use std::{env, process::exit};

use ariadne::{Label, Report, ReportKind, Source};
use common::Error;

mod analyzer;
mod ast;
mod common;
mod lexer;
mod parser;
mod token;

fn report_error_and_exit(src: &str, err: Error) -> ! {
    Report::build(ReportKind::Error, (), err.span.start)
        .with_label(Label::new(err.span).with_message(err.message))
        .finish()
        .print(Source::from(src))
        .unwrap();

    exit(1);
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        eprintln!(
            r#"
Usage:

{} [filename]

Arguments:

filename = Path to the file that you would like to compile
"#,
            args[0]
        );
        exit(1);
    }

    let mut file = match ast::File::new(&args[1]) {
        Ok(file) => file,
        Err(err) => {
            eprintln!("{}", err.to_string());
            exit(1);
        }
    };

    let tokens = match lexer::lex(&file.source) {
        Ok(tokens) => tokens,
        Err(err) => report_error_and_exit(&file.source, err),
    };

    file.stmts = match parser::parse(&tokens) {
        Ok(stmts) => stmts,
        Err(err) => report_error_and_exit(&file.source, err),
    };

    if let Err(err) = analyzer::analyze_mut(&mut file) {
        report_error_and_exit(&file.source, err)
    };
}
