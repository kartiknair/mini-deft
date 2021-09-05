use ariadne::{Label, Report, ReportKind, Source};
use common::Error;

mod ast;
mod common;
mod lexer;
mod token;

fn report_error_and_exit(src: &str, err: Error) {
    Report::build(ReportKind::Error, (), err.span.start)
        .with_label(Label::new(err.span).with_message(err.message))
        .finish()
        .print(Source::from(src))
        .unwrap();
}

fn main() {
    let demo_src = r#"
        extern fun printi32(n i32)

        fun fib(n i32) i32 {
            if n < 2 {
                return ""
            }

            return fib(n-1) + fib(n-2)
        }

        fun main() {
            printi32(fib(20))
            retEarly()
        }
    "#;

    match lexer::lex(demo_src) {
        Ok(tokens) => {
            dbg!(&tokens);
        }
        Err(err) => {
            report_error_and_exit(demo_src, err);
        }
    }
}
