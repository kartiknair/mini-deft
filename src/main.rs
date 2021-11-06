use std::{env, process::exit};

use ariadne::{Label, Report, ReportKind, Source};
use common::Error;

mod analyzer;
mod ast;
mod codegen;
mod common;
mod lexer;
mod parser;
mod token;

fn report_error_and_exit(src: &str, err: Error, filename: &str) -> ! {
    Report::build(ReportKind::Error, filename, err.span.start)
        .with_label(Label::new((filename, err.span)).with_message(err.message))
        .finish()
        .print((filename, Source::from(src)))
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

    let filename = &args[1];
    let mut file = match ast::File::new(&args[1]) {
        Ok(file) => file,
        Err(err) => {
            eprintln!("{}", err.to_string());
            exit(1);
        }
    };
    dbg!("done reading source file");

    let tokens = match lexer::lex(&file.source) {
        Ok(tokens) => tokens,
        Err(err) => report_error_and_exit(&file.source, err, filename),
    };
    dbg!("done tokenizing");

    file.stmts = match parser::parse(&tokens) {
        Ok(stmts) => stmts,
        Err(err) => report_error_and_exit(&file.source, err, filename),
    };
    dbg!("done parsing");

    if let Err(err) = analyzer::analyze_mut(&mut file) {
        report_error_and_exit(&file.source, err, filename)
    };
    dbg!("done analyzing");

    let context = inkwell::context::Context::create();
    let llvm_module = codegen::gen(&context, &file);

    // since `dbg!()` makes it harder to read the IR
    if cfg!(debug_assertions) {
        println!("{}", llvm_module.print_to_string().to_string());
    }

    let execution_engine = llvm_module
        .create_jit_execution_engine(inkwell::OptimizationLevel::None)
        .expect("internal-error: could not create execution engine");

    // SAFETY: It is inherently unsafe to call a JIT function for the same reason calling any external C function would be.
    unsafe {
        type LLVMMain = unsafe extern "C" fn() -> i32;

        if let Ok(main_func) = execution_engine.get_function::<LLVMMain>("main") {
            let ret_value = main_func.call();
            exit(ret_value);
        };
    }
}
