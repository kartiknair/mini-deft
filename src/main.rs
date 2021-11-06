use std::{
    env,
    process::{self, exit},
};

use ariadne::{Label, Report, ReportKind, Source};
use common::Error;
use inkwell::{
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine},
    OptimizationLevel,
};
use seahorse::{App, Command, Flag, FlagType};

mod analyzer;
mod ast;
mod codegen;
mod common;
mod lexer;
mod parser;
mod token;

fn report_error_and_exit(err: Error, src: &str, filename: &str) -> ! {
    Report::build(ReportKind::Error, filename, err.span.start)
        .with_label(Label::new((filename, err.span)).with_message(err.message))
        .finish()
        .print((filename, Source::from(src)))
        .unwrap();

    exit(1);
}

fn llvm_module_from_filename<'ctx>(
    filename: &str,
    context: &'ctx inkwell::context::Context,
) -> inkwell::module::Module<'ctx> {
    let mut file = match ast::File::new(filename.to_string()) {
        Ok(file) => file,
        Err(err) => {
            eprintln!("{}", err.to_string());
            exit(1);
        }
    };

    let tokens = match lexer::lex(&file.source) {
        Ok(tokens) => tokens,
        Err(err) => report_error_and_exit(err, &file.source, filename),
    };

    file.stmts = match parser::parse(&tokens) {
        Ok(stmts) => stmts,
        Err(err) => report_error_and_exit(err, &file.source, filename),
    };

    if let Err(err) = analyzer::analyze_mut(&mut file) {
        report_error_and_exit(err, &file.source, filename)
    };

    codegen::gen(context, &file)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let app = App::new(env!("CARGO_PKG_NAME"))
        .description(env!("CARGO_PKG_DESCRIPTION"))
        .author(env!("CARGO_PKG_AUTHORS"))
        .version(env!("CARGO_PKG_VERSION"))
        .usage("deft <command> [options...]")
        .command(
            Command::new("build")
                .description("")
                .usage("deft build <filename> [options...]")
                .action(|c| {
                    let linker = c.string_flag("linker").unwrap_or_else(|_| "cc".to_string());
                    let linker_artifacts = c
                        .string_flag("linker-artifacts")
                        .unwrap_or_else(|_| "".to_string());
                    let exe_path = c
                        .string_flag("outfile")
                        .unwrap_or_else(|_| "a.out".to_string());

                    let context = inkwell::context::Context::create();
                    let llvm_module = llvm_module_from_filename(&c.args[0], &context);

                    Target::initialize_native(&InitializationConfig::default()).unwrap();

                    let opt = OptimizationLevel::Default;
                    let reloc = RelocMode::Default;
                    let model = CodeModel::Default;
                    let target = Target::from_triple(&TargetMachine::get_default_triple()).unwrap();
                    let target_machine = target
                        .create_target_machine(
                            &TargetMachine::get_default_triple(),
                            &TargetMachine::get_host_cpu_name().to_string(),
                            &TargetMachine::get_host_cpu_features().to_string(),
                            opt,
                            reloc,
                            model,
                        )
                        .unwrap();

                    let tmp_dir = env::temp_dir();
                    let obj_path = {
                        let mut file_path = tmp_dir;
                        file_path.push("deft_tmp_obj.o");
                        file_path
                    };

                    target_machine
                        .write_to_file(&llvm_module, FileType::Object, obj_path.as_path())
                        .unwrap();

                    let mut linker_args = vec![obj_path.as_os_str().to_str().unwrap()];
                    for artifact in linker_artifacts.split_ascii_whitespace() {
                        linker_args.push(artifact);
                    }
                    linker_args.push("-o");
                    linker_args.push(&exe_path);

                    let link_output = process::Command::new(linker)
                        .args(&linker_args)
                        .output()
                        .expect("failed to execute linker command");

                    if cfg!(debug_assertions) {
                        if !link_output.stdout.is_empty() {
                            println!("{}", String::from_utf8_lossy(&link_output.stdout));
                        }
                        if !link_output.stderr.is_empty() {
                            println!("{}", String::from_utf8_lossy(&link_output.stderr));
                        }
                    }
                })
                .flag(
                    Flag::new("linker", FlagType::String)
                        .description("Change the linker used (default: cc)"),
                )
                .flag(
                    Flag::new("linker-artifacts", FlagType::String)
                        .description("Artifacts that should be linked into the final executable"),
                )
                .flag(
                    Flag::new("outfile", FlagType::String)
                        .description("Rename the output executable file (default: a.out)")
                        .alias("o"),
                ),
        )
        .command(
            Command::new("emit-llvm")
                .description("Generate and print the LLVM IR for a given file.")
                .usage("deft emit-llvm <filename> [options...]")
                .action(|c| {
                    let context = inkwell::context::Context::create();
                    let llvm_module = llvm_module_from_filename(&c.args[0], &context);
                    println!("{}", llvm_module.print_to_string().to_string())
                }),
        );

    app.run(args);
}
