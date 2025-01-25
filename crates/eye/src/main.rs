/// command line argument parsing
mod args;

use std::{
    ffi::CString,
    path::{Path, PathBuf},
};

use args::Backend;
pub use compiler::{Compiler, Span};

use compiler::Def;

use compiler::error::Error;

#[derive(Debug)]
pub enum MainError {
    CantAccessPath(std::io::Error, PathBuf),
    NonexistentPath(PathBuf),
    MissingProjectDirectoryName(PathBuf),
    MissingProjectFileName(PathBuf),
    NoMainFileInProjectDirectory,
    InvalidPath(PathBuf),
    ErrorsFound,
    BackendFailed(String),
    LinkingFailed(String),
    RunningProgramFailed(std::io::Error),
    LspFailed(String),
}
impl From<compiler::ProjectError> for MainError {
    fn from(value: compiler::ProjectError) -> Self {
        match value {
            compiler::ProjectError::CantAccessPath(err, path) => Self::CantAccessPath(err, path),
            compiler::ProjectError::NonexistentPath(path) => Self::NonexistentPath(path),
        }
    }
}

fn main() -> Result<(), MainError> {
    let args: args::Args = clap::Parser::parse();
    match args.cmd {
        args::Cmd::ListTargets => {
            list_targets(args.backend);
            return Ok(());
        }
        #[cfg(feature = "lsp")]
        args::Cmd::Lsp => {
            return eye_lsp::run().map_err(|err| MainError::LspFailed(format!("{err:?}")));
        }
        _ => {}
    }
    if let args::Cmd::ListTargets = args.cmd {
        list_targets(args.backend);
        return Ok(());
    }
    let start_time = std::time::Instant::now();
    let mut compiler = compiler::Compiler::new();
    if args.crash_on_error {
        eprintln!("enabling crash on error");
        compiler.errors.enable_crash_on_error();
    }

    let (name, path) = match &args.path {
        Some(path_str) => {
            let path = Path::new(path_str);
            if !path
                .try_exists()
                .map_err(|err| MainError::CantAccessPath(err, path.to_path_buf()))?
            {
                return Err(MainError::NonexistentPath(path.to_owned()));
            }
            let name = if path.is_file() {
                path.file_stem()
                    .ok_or_else(|| MainError::MissingProjectFileName(path.to_path_buf()))?
                    .to_str()
                    .ok_or_else(|| MainError::InvalidPath(path.to_path_buf()))?
            } else {
                path.file_name()
                    .ok_or_else(|| MainError::MissingProjectDirectoryName(path.to_path_buf()))?
                    .to_str()
                    .ok_or_else(|| MainError::InvalidPath(path.to_path_buf()))?
            };
            (name, path)
        }
        None => ("main", Path::new("./")),
    };

    // create project
    let project = compiler.add_project(name.to_owned(), path.to_path_buf())?;
    let root_module = compiler.get_project(project).root_module;

    println!("Compiling {} ...", name);

    // add standard library
    let std_path = std::env::current_exe()
        .ok()
        .and_then(|path| path.parent().map(|path| path.join("std/")))
        .and_then(|std_path| {
            std_path
                .try_exists()
                .is_ok_and(|exists| exists)
                .then_some(std_path)
        })
        .unwrap_or(PathBuf::from("std/"));
    let std = compiler.add_project("std".to_owned(), std_path)?;
    compiler.add_dependency(project, std);
    compiler.builtins.set_std(std);

    if args.reconstruct_src {
        let ast = compiler.get_module_ast(root_module);
        compiler::ReprPrinter::new("  ", ast).print_module();
    }

    // always check the complete project
    compiler.check_complete_project(project);

    // check that the main function exists if we are not compiling a library
    let main = (!args.lib)
        .then(|| {
            let main_def =
                compiler.resolve_in_module(root_module, "main", Span::new(0, 0, root_module));
            let (main_module, main_id) = match main_def {
                Def::Function(main_module, main_id) => (main_module, main_id),
                Def::Invalid => {
                    compiler.print_errors();
                    return Err(MainError::ErrorsFound);
                }
                other => {
                    // unwrapping is fine, only returns none when the Def is invalid
                    let span = other.get_span(&mut compiler).unwrap();

                    compiler
                        .errors
                        .emit_err(Error::MainIsNotAFunction.at_span(span));
                    compiler.print_errors();
                    return Err(MainError::ErrorsFound);
                }
            };
            let signature = compiler.get_signature(main_module, main_id);
            if let Err(err) = compiler::check::verify_main_signature(signature, main_module) {
                if let Some(error) = err {
                    compiler.errors.emit_err(error);
                }
                compiler.print_errors();
                return Err(MainError::ErrorsFound);
            }
            Ok((main_module, main_id))
        })
        .transpose()?;

    if args.hir {
        compiler.print_project_hir(project);
    }
    if args.ir {
        // TODO: right now, backends just codegen all functions that are emitted so this causes
        // functions to be emitted unnecessarily. Could maybe be solved by collecting a list of ir
        // function ids required for compiling main and passing it to the backend.
        compiler.emit_whole_project_ir(project);
        println!(
            "Displaying IR:\n{}",
            compiler.ir.display_module(compiler.ir_module)
        );
    }
    if compiler.print_errors() && !args.run_with_errors {
        return Err(MainError::ErrorsFound);
    }

    match args.cmd {
        args::Cmd::Check => {}
        args::Cmd::Build | args::Cmd::Run => {
            if let Some(main) = main {
                compiler.emit_ir_from_root(main);
                // verification was already done so the error can be ignored here
                _ = compiler.verify_main_and_add_entry_point(main);
            } else {
                compiler.emit_whole_project_ir(project);
            }
            #[cfg(debug_assertions)]
            ir::verify::module(&compiler.ir, compiler.ir_module);

            if args.optimize {
                let mut pipeline = ir::optimize::Pipeline::optimizing(&mut compiler.ir);
                if args.passes {
                    pipeline.enable_print_passes();
                }
                pipeline.optimize_module(&mut compiler.ir, compiler.ir_module);

                #[cfg(debug_assertions)]
                ir::verify::module(&compiler.ir, compiler.ir_module);
            }

            if compiler.print_errors() && !args.run_with_errors {
                return Err(MainError::ErrorsFound);
            }
            std::fs::create_dir_all(Path::new("eyebuild")).unwrap();
            let obj_file = format!("eyebuild/{name}.o");
            match args.backend {
                Backend::C => todo!("reimplement C backend"),
                #[cfg(feature = "fast-backend")]
                Backend::Fast => {
                    let mut backend = ir_backend_fast::Backend::new();
                    if args.log {
                        backend.enable_logging();
                    }
                    backend
                        .emit_module(
                            &mut compiler.ir,
                            compiler.ir_module,
                            args.backend_ir,
                            args.target.as_deref(),
                            Path::new(&obj_file),
                        )
                        .map_err(|err| MainError::BackendFailed(format!("{err:?}")))?;
                }
                #[cfg(feature = "llvm-backend")]
                Backend::Llvm => {
                    let mut backend = ir_backend_llvm::Backend::new();
                    if args.log {
                        backend.enable_logging();
                    }
                    let target = args.target.as_ref().map(|target| {
                        CString::new(target.as_bytes()).expect("invalid target string")
                    });
                    backend
                        .emit_module(
                            &compiler.ir,
                            compiler.ir_module,
                            args.backend_ir,
                            target.as_deref(),
                            Path::new(&obj_file),
                        )
                        .map_err(|err| MainError::BackendFailed(format!("{err:?}")))?;
                }
            }
            if args.timings {
                eprintln!("Compiling took {:?}", start_time.elapsed());
            }
            if args.emit_obj || args.lib {
                return Ok(());
            }
            #[cfg(not(target_os = "windows"))]
            let exe_file_extension = "";
            #[cfg(target_os = "windows")]
            let exe_file_extension = ".exe";
            let exe_file = format!("eyebuild/{name}{exe_file_extension}");
            if let Err(err) =
                compiler::link(&obj_file, &exe_file, args.link_cmd.as_deref(), &args.link)
            {
                return Err(MainError::LinkingFailed(err));
            }
            if args.cmd == args::Cmd::Run {
                println!("Running {}...", name);
                // make sure to clean up compiler resources before running
                drop(compiler);
                let mut command = std::process::Command::new(exe_file);

                #[cfg(target_family = "unix")]
                {
                    let err = std::os::unix::process::CommandExt::exec(&mut command);
                    return Err(MainError::RunningProgramFailed(err));
                }
                #[cfg(not(target_family = "unix"))]
                {
                    let exit_code = command
                        .status()
                        .map_err(MainError::RunningProgramFailed)?
                        .code()
                        .unwrap_or(0);
                    std::process::exit(exit_code);
                }
            }
        }
        args::Cmd::ListTargets => unreachable!(),
        #[cfg(feature = "lsp")]
        args::Cmd::Lsp => unreachable!(),
    }

    Ok(())
}

fn list_targets(backend: args::Backend) {
    let targets = match backend {
        Backend::C => vec!["C".to_owned()],
        #[cfg(feature = "llvm-backend")]
        Backend::Llvm => ir_backend_llvm::list_targets(),
        #[cfg(feature = "fast-backend")]
        Backend::Fast => ir_backend_fast::list_targets(),
    };
    println!(
        "Available targets for {backend} backend: (total: {})",
        targets.len()
    );
    for target in targets {
        println!("\t{target}");
    }
}
