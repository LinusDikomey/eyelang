#![feature(
    variant_count,
    fs_try_exists,
    int_roundings,
    array_chunks,
    if_let_guard,
    slice_as_chunks,
)]
#![warn(unused_qualifications)]

mod ast;
mod backend;
mod compile;
mod dmap;
mod error;
mod help;
mod ir;
mod irgen;
mod lexer;
mod link;
#[cfg(feature = "lsp")]
mod lsp;
mod parser;
mod resolve;
mod span;
mod token;
mod types;

#[cfg(feature = "llvm-backend")]
extern crate llvm_sys as llvm;

use color_format::*;
use std::{
    fmt,
    path::{Path, PathBuf},
    sync::atomic::AtomicBool,
    time::{Duration, Instant},
};

static LOG: AtomicBool = AtomicBool::new(false);
static DEBUG_INFER: AtomicBool = AtomicBool::new(false);
static CRASH_ON_ERROR: AtomicBool = AtomicBool::new(false);

macro_rules! log {
    () => {
        if $crate::LOG.load(std::sync::atomic::Ordering::Relaxed) { println!() }
    };
    ($s: expr $(,$arg: expr)*) => {
        if $crate::LOG.load(std::sync::atomic::Ordering::Relaxed) { println!($s, $($arg),*) }
    }
}
pub(crate) use log;

const SEPARATOR_LINE: &str = "------------------------------\n";

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
enum Cmd {
    /// Check a file or project for errors and warnings.
    Check,
    /// Build an executable and run it immediately.
    Run,
    /// Build an executable.
    Build,
    /// Compile and run using LLVMs JIT compiler. Might produce different results.
    Jit,
    /// Starts a language server that can be used by IDEs for syntax highlighting, autocompletions etc.
    /// Only basic error highlighting is implemented right now.
    #[cfg(feature = "lsp")]
    Lsp,
}
impl Default for Cmd {
    fn default() -> Self {
        Self::Check
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
pub enum Backend {
    // Emit C code
    C,

    // Run with the llvm backend
    #[cfg(feature = "llvm-backend")]
    LLVM,
    /// W.I.P.! Run with a self-implemented x86 backend. Will emit completely unoptimized code.
    /// This backend is primarily used for fast compilations. It is mostly unfinished right now.
    X86,
}
impl fmt::Display for Backend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match *self {
            Self::C => "C",
            #[cfg(feature = "llvm-backend")]
            Self::LLVM => "LLVM",
            Self::X86 => "x86",
        };
        f.write_str(s)
    }
}
impl Default for Backend {
    fn default() -> Self {
        #[cfg(feature = "llvm-backend")]
        {
            Self::LLVM
        }

        #[cfg(not(feature = "llvm-backend"))]
        {
            Self::X86
        }
    }
}

#[derive(clap::Parser)]
#[clap(
    version,
    about,
    long_about = "Eye is a simple, compiled, performant programming language"
)]
#[allow(clippy::struct_excessive_bools)]
#[derive(Default)]
pub struct Args {
    #[clap(value_enum)]
    cmd: Cmd,
    file: Option<String>,

    /// Enable debug logging
    #[clap(long)]
    log: bool,

    /// Used for providing a custom link command. Use '[OBJ]' and '[OUT]' as placeholders for object and out file.
    /// Example: --link-cmd "ld [OBJ] -lc -o [OUT]"
    #[clap(long)]
    link_cmd: Option<String>,

    /// Disables the standard library
    #[clap(long)]
    nostd: bool,

    /// Just emit an object file. Doesn't require a main function
    #[clap(long)]
    emit_obj: bool,

    /// Library that doesn't require a main function.
    #[clap(long)]
    lib: bool,

    /// Report compilation times of all files/compilation steps.
    #[clap(long)]
    timings: bool,

    /// prints out all tokens after lexing.
    #[clap(short, long)]
    tokens: bool,

    /// Reconstructs the src using the abstract syntax tree information. Can be used to test parser correctness.
    #[clap(short, long)]
    reconstruct_src: bool,

    /// Debug the type inferer.
    #[clap(long)]
    debug_infer: bool,

    /// Print the internal IR (intermediate representation) to stderr.
    /// This will still normally execute the subcommand.
    #[clap(long)]
    ir: bool,

    /// Print the IR of the selected backend (if the backend creates an ir) to stderr.
    /// This will still normally execute the subcommand.
    #[clap(long)]
    backend_ir: bool,

    /// Crash once a single error is encountered. Mostly used for debugging the compiler.
    #[clap(long)]
    crash_on_error: bool,

    /// Libraries to link against
    #[clap(short, long)]
    link: Vec<String>,

    #[cfg_attr(
        feature = "llvm-backend",
        clap(short, long, value_enum, default_value_t = Backend::LLVM)
    )]
    #[cfg_attr(
        not(feature = "llvm-backend"),
        clap(short, long, value_enum, default_value_t = Backend::X86)
    )]
    backend: Backend,
}

fn main() {
    let args: Args = clap::Parser::parse();
    DEBUG_INFER.store(args.debug_infer, std::sync::atomic::Ordering::Relaxed);
    LOG.store(args.log, std::sync::atomic::Ordering::Relaxed);
    CRASH_ON_ERROR.store(args.crash_on_error, std::sync::atomic::Ordering::Relaxed);

    if let Err(err) = run(&args) {
        eprintln!("sus");
        ceprintln!("#underline;red<Error>: {err}");
        std::process::exit(42)
    }
}

type RunResult = Result<(), &'static str>;

fn run(args: &Args) -> RunResult {
    #[cfg(feature = "lsp")]
    if let Cmd::Lsp = args.cmd {
        return match lsp::lsp(args) {
            Ok(()) => Ok(()),
            Err(err) => {
                lsp::debug(format!("Exited with err: {:?}", err));
                Err("LSP exited with error")
            }
        };
    }

    let path = Path::new(args.file.as_deref().unwrap_or("./"));

    let no_extension = path.with_extension("");
    let name = no_extension
        .file_name()
        .expect("Failed to retrieve filename for input file")
        .to_str()
        .expect("Invalid filename");

    cprintln!("#g<Compiling> #u;b!<{}> ...", name);

    run_path(path, args, name)
}

#[derive(Default)]
pub struct Stats {
    file_times: Vec<FileStats>,
    resolve: Duration,
    irgen: Duration,
}
impl fmt::Display for Stats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "{SEPARATOR_LINE}\
            Timings of {} files:",
            self.file_times.len()
        )?;
        let mut overall_lex = Duration::ZERO;
        let mut overall_parse = Duration::ZERO;

        for file in &self.file_times {
            writeln!(
                f,
                "\t{}: {:?} (lex: {:?}, parse: {:?})",
                file.name,
                file.lex + file.parse,
                file.lex,
                file.parse
            )?;
            overall_lex += file.lex;
            overall_parse += file.parse;
        }
        write!(
            f,
            "\nOverall: {:?}:\n\tlex: {:?}\n\tparse: {:?}\n\tresolve: {:?}\n\tirgen: {:?}\n\
            {SEPARATOR_LINE}",
            overall_lex + overall_parse + self.resolve + self.irgen,
            overall_lex,
            overall_parse,
            self.resolve,
            self.irgen,
        )
    }
}

pub struct FileStats {
    name: String,

    lex: Duration,
    parse: Duration,
}

pub struct BackendStats {
    name: &'static str,
    init: Duration,
    type_creation: Duration,
    func_header_creation: Duration,
    emit: Duration,
}
impl fmt::Display for BackendStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "{SEPARATOR_LINE}Backend Timings ({}):",
            self.name
        )?;
        writeln!(f, "\tInit: {:?}", self.init)?;
        writeln!(f, "\tType creation: {:?}", self.type_creation)?;
        writeln!(
            f,
            "\tFunction header creation: {:?}",
            self.func_header_creation
        )?;
        writeln!(f, "\tEmit: {:?}", self.emit)?;
        write!(
            f,
            "Overall: {:?}\n{SEPARATOR_LINE}",
            self.init + self.type_creation + self.func_header_creation + self.emit
        )
    }
}

fn run_path(path: &Path, args: &Args, project_name: &str) -> RunResult {
    let mut stats = Stats::default();
    let (project, ast) = {
        let debug_options = compile::Debug {
            tokens: args.tokens,
            reconstruct_src: args.reconstruct_src,
        };
        let mut dependencies = dmap::new();
        let is_std = if let Some(name) = path.file_name() { name == "std" } else { false };
        
        if !args.nostd && !is_std {
            dependencies.insert("std".to_owned(), compile::Dependency { path: std_path(), is_std: true });
        }
        let (res, ast, errors) = compile::project(
            path,
            debug_options,
            dependencies,
            !args.emit_obj && !args.lib,
            &mut stats,
            is_std,
        );
        if errors.error_count() > 0 {
            errors.print(&ast);
            return Err("Compiler exited with errors")
        } else if errors.warning_count() > 0 {
            errors.print(&ast);
        }
        match res {
            Ok(project) => (project, ast),
            Err(()) => return Err("Compiler exited with errors"),
        }
    };

    match (args.cmd, args.backend) {
        (Cmd::Check, _) => cprintln!("#g<Check successful ✅>"),
        (Cmd::Run | Cmd::Build | Cmd::Jit, _) => {
            let reduce_start_time = Instant::now();
            let ir = project.ir.finish_module(project.symbols, &ast, project.main);
            stats.irgen += reduce_start_time.elapsed();

            if args.ir {
                eprintln!("\n\n{ir}\n");
            }
            build_project(args, &ir, project_name)?;
        }
        #[cfg(feature = "lsp")]
        (Cmd::Lsp, _) => unreachable!(),
    }

    if args.timings {
        println!("{stats}");
    }

    Ok(())
}

fn build_project(args: &Args, ir: &ir::Module, project_name: &str) -> RunResult {
    let obj_file = format!("eyebuild/{project_name}.o");
    let exe_file = format!("eyebuild/{project_name}");

    let jit = args.cmd == Cmd::Jit;

    // create eyebuild directory
    if !jit && !std::fs::try_exists("eyebuild")
        .expect("Failed to check availability of eyebuild directory")
    {
        match std::fs::create_dir("eyebuild") {
            Ok(()) => (),
            Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists => (),
            Err(_) => return Err("Failed to create eyebuild directory"),
        }
    }

    if jit {
        if args.lib {
            return Err("There is nothing to run in the jit because --lib was passed");
        }
        let is_llvm;
        #[cfg(feature = "llvm-backend")]
        { is_llvm = args.backend == Backend::LLVM }
        #[cfg(not(feature = "llvm-backend"))]
        { is_llvm = false }
        
        if !is_llvm {
            return Err("This backend doesn't support running via JIT. Only the LLVM backend supports JIT right now");
        }
    }
    
    let params = BackendParams {
        timings: args.timings,
        show_backend_ir: args.backend_ir,
        jit,
        obj_file: &obj_file,
        project_name,
    };

    run_backend(ir, args.backend, params)?;
    if args.cmd == Cmd::Jit {
        // we are finished
        return Ok(());
    }

    if args.emit_obj {
        cprintln!("#g<Object successfully emitted!>");
        return Ok(());
    }

    link::link(&obj_file, &exe_file, args)?;

    if args.cmd == Cmd::Run {
        if args.lib {
            return Err("There is nothing to run> because --lib was passed");
        }
        cprintln!("#g<Running {}>...", project_name);
        execute_file(&exe_file);
    } else {
        cprintln!("#g<Built #u<{}>>", project_name);
    }
    Ok(())
}

fn execute_file(file: impl AsRef<Path>) -> ! {
    let mut command = std::process::Command::new(file.as_ref());
    // use the exec() syscall on unix systems or just spawn a child process and pass on it's exit code otherwise.
    #[cfg(unix)]
    {
        let error = std::os::unix::prelude::CommandExt::exec(&mut command);
        panic!("Failed to exec the executable command: {error:?}");
    }
    #[cfg(not(unix))]
    {
        let status = command
            .spawn()
            .expect("Failed to run the executable command")
            .wait()
            .expect("Running process failed");
        std::process::exit(status.code().unwrap_or(0));
    }
}

struct BackendParams<'a> {
    timings: bool,
    show_backend_ir: bool,
    jit: bool,
    obj_file: &'a str,
    project_name: &'a str,
}

fn run_backend(ir: &ir::Module, backend: Backend, params: BackendParams) -> RunResult {
    match backend {
        #[cfg(feature = "llvm-backend")]
        Backend::LLVM => unsafe {
            let context = llvm::core::LLVMContextCreate();
            let (llvm_module, stats) = backend::llvm::module(context, ir, params.show_backend_ir);
            if params.timings {
                println!("{stats}");
            }
            if params.jit {
                cprintln!("#g<JIT running>...");
                let ret_val = backend::llvm::output::run_jit(llvm_module);
                llvm::core::LLVMContextDispose(context);

                std::process::exit(ret_val as i32);
            } else {
                let bitcode_emit_start_time = std::time::Instant::now();
                backend::llvm::output::emit_bitcode(None, llvm_module, params.obj_file);
                if params.timings {
                    println!(
                        "LLVM backend bitcode emit time: {:?}",
                        bitcode_emit_start_time.elapsed()
                    );
                }
                llvm::core::LLVMContextDispose(context);
            }
        }
        Backend::C => {
            let c_path = PathBuf::from(format!("./eyebuild/{}.c", params.project_name));
            let file = std::fs::File::create(&c_path).expect("Couldn't create C file");
            backend::c::emit(ir, file).expect("Failed to emit C code");
            let status = std::process::Command::new("gcc")
                .arg(c_path)
                .arg("-c") // generate an object file
                .args(["-o", params.obj_file])
                .status()
                .expect("Failed to compile C code using gcc");

            if !status.success() {
                return Err("gcc failed");
            }
        }
        Backend::X86 => {
            let asm_file = format!("eyebuild/{}.asm", params.project_name);
            backend::x86_64::generate(ir, &asm_file, params.obj_file)?;
        }
    }
    Ok(())
}

fn std_path() -> PathBuf {
    match std::env::current_exe()
        .ok()
        .and_then(|path| path.parent().map(|p| Path::join(p, "std")))
    {
        Some(path) => match std::fs::try_exists(&path) {
            Ok(true) => path,
            _ => "std".into(),
        },
        _ => "std".into(),
    }
}
