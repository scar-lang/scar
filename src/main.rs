mod ast;
mod clif;
mod codegen;
mod lexer;
mod parser;
mod resolver;
mod sema;
mod wasm;

use std::{
    collections::hash_map::DefaultHasher,
    env, fs,
    hash::{Hash, Hasher},
    path::{Path, PathBuf},
    process::{Command, ExitCode},
};

use ast::{Expr, Function, Program, Stmt, Type};
use codegen::generate_c;
use lexer::lex;
use parser::parse_program;
use resolver::resolve_entry_program;
use sema::analyze;

#[derive(Debug, Clone)]
pub struct CompileError {
    message: String,
    location: Option<SourceLocation>,
    pub file_path: Option<PathBuf>,
}

impl CompileError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            location: None,
            file_path: None,
        }
    }

    pub fn with_location(mut self, line: usize, column: usize) -> Self {
        if self.location.is_none() {
            self.location = Some(SourceLocation { line, column });
        }
        self
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn location(&self) -> Option<(usize, usize)> {
        self.location
            .map(|location| (location.line, location.column))
    }

    pub fn with_file(mut self, file_path: impl Into<PathBuf>) -> Self {
        if self.file_path.is_none() {
            self.file_path = Some(file_path.into());
        }
        self
    }

    pub fn with_file_opt(mut self, file_path: Option<PathBuf>) -> Self {
        if self.file_path.is_none() {
            self.file_path = file_path;
        }
        self
    }
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for CompileError {}

#[derive(Debug)]
pub struct CompileErrors {
    pub errors: Vec<CompileError>,
}

impl std::fmt::Display for CompileErrors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(error) = self.errors.first() {
            write!(f, "{}", error.message())
        } else {
            write!(f, "unknown error")
        }
    }
}

impl CompileErrors {
    const MAX: usize = 50;

    pub fn new() -> Self {
        CompileErrors { errors: Vec::new() }
    }

    pub fn single(error: CompileError) -> Self {
        CompileErrors {
            errors: vec![error],
        }
    }

    pub fn push(&mut self, error: CompileError) {
        if self.errors.len() < Self::MAX {
            self.errors.push(error);
        }
    }

    pub fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }

    pub fn len(&self) -> usize {
        self.errors.len()
    }

    pub fn is_full(&self) -> bool {
        self.errors.len() >= Self::MAX
    }

    pub fn extend(&mut self, other: CompileErrors) {
        for e in other.errors {
            self.push(e);
        }
    }
}

fn main() -> ExitCode {
    let cli = match Cli::parse(env::args().skip(1)) {
        Ok(cli) => cli,
        Err(error) => {
            eprintln!("{}", format_compile_error(&error, None));
            return ExitCode::FAILURE;
        }
    };

    match run(&cli) {
        Ok(()) => ExitCode::SUCCESS,
        Err(errors) => {
            let default_path = cli.default_error_path();
            for error in &errors.errors {
                eprintln!("{}", format_compile_error(error, default_path));
            }
            ExitCode::FAILURE
        }
    }
}

fn run(cli: &Cli) -> Result<(), CompileErrors> {
    match cli {
        Cli::Build(cli) => run_build(cli),
        Cli::Wasm(cli) => run_wasm_command(cli),
        Cli::Ast(cli) => run_ast_command(cli),
        Cli::Inspect(cli) => run_inspect_command(cli),
        Cli::Run(cli) => run_run_command(cli),
        Cli::Test(cli) => run_test_command(cli),
        Cli::Help => {
            print_help();
            Ok(())
        }
        Cli::Version => {
            print_version();
            Ok(())
        }
    }
}

fn print_version() {
    println!(
        "scar v{} ({})",
        env!("CARGO_PKG_VERSION"),
        env!("SCAR_GIT_COMMIT")
    );
}

fn print_help() {
    print_version();
    println!("\n(C) Navid Momtahen - 2026\n");
    println!("Usage: scar <command> [options]");
    println!();
    println!("Commands:");
    println!("  build <file.scar>    Build a native executable");
    println!("  wasm  <file.scar>    Compile to WebAssembly");
    println!("  ast   <file.scar>    Print the parsed AST");
    println!("  inspect <file.scar>  Print the Cranelift IR");
    println!("  run   <file.scar>    Compile and run a program");
    println!("  test  <file|dir>     Run test blocks");
    println!("  help                 Show this help message");
    println!("  version              Show version information");
    println!();
    println!("Options:");
    println!("  -o, --output <path>  Write output to <path>");
    println!("  -opt, --opt          Enable optimizations");
    println!("  -c                   Use the legacy native backend (build only)");
}

#[derive(Debug, Clone, Copy)]
struct SourceLocation {
    line: usize,
    column: usize,
}

enum Cli {
    Build(BuildCli),
    Wasm(WasmCli),
    Ast(AstCli),
    Inspect(InspectCli),
    Run(RunCli),
    Test(TestCli),
    Help,
    Version,
}

impl Cli {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, CompileError> {
        let args: Vec<String> = args.collect();
        let Some(command) = args.first() else {
            return Ok(Self::Help);
        };
        match command.as_str() {
            "build" => Ok(Self::Build(BuildCli::parse(args.into_iter().skip(1))?)),
            "wasm" => Ok(Self::Wasm(WasmCli::parse(args.into_iter().skip(1))?)),
            "ast" => Ok(Self::Ast(AstCli::parse(args.into_iter().skip(1))?)),
            "inspect" => Ok(Self::Inspect(InspectCli::parse(args.into_iter().skip(1))?)),
            "run" => Ok(Self::Run(RunCli::parse(args.into_iter().skip(1))?)),
            "test" => Ok(Self::Test(TestCli::parse(args.into_iter().skip(1))?)),
            "help" | "-h" | "--help" => Ok(Self::Help),
            "version" | "-V" | "--version" => Ok(Self::Version),
            _ if command.ends_with(".scar") => Ok(Self::Build(BuildCli::parse(args.into_iter())?)),
            _ => Ok(Self::Help),
        }
    }

    fn default_error_path(&self) -> Option<&Path> {
        match self {
            Cli::Build(cli) => Some(&cli.input),
            Cli::Wasm(cli) => Some(&cli.input),
            Cli::Ast(cli) => Some(&cli.input),
            Cli::Inspect(cli) => Some(&cli.input),
            Cli::Run(cli) => Some(&cli.input),
            Cli::Test(cli) => Some(&cli.target),
            Cli::Help | Cli::Version => None,
        }
    }
}

struct BuildCli {
    input: PathBuf,
    output: PathBuf,
    emit_c: bool,
    use_c: bool,
    optimize: bool,
}

impl BuildCli {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, CompileError> {
        let mut input = None;
        let mut output = None;
        let mut pending_output = false;
        let mut emit_c = false;
        let mut use_c = false;
        let mut optimize = false;

        for arg in args {
            if pending_output {
                output = Some(PathBuf::from(arg));
                pending_output = false;
                continue;
            }

            match arg.as_str() {
                "-o" | "--output" => pending_output = true,
                "-opt" | "--opt" => optimize = true,
                "-c" | "--c-backend" => use_c = true,
                "--emit" | "-emit" => emit_c = true,
                _ if arg.starts_with('-') => {
                    return Err(CompileError::new(format!("unknown flag: {arg}")));
                }
                _ => {
                    if input.is_some() {
                        return Err(CompileError::new(
                            "expected a single input file and optional -o/--output path",
                        ));
                    }
                    input = Some(PathBuf::from(arg));
                }
            }
        }

        if pending_output {
            return Err(CompileError::new("expected a path after -o/--output"));
        }
        if emit_c {
            use_c = true;
        }

        let input = input.ok_or_else(|| {
            CompileError::new("usage: scar build <input.scar> [-opt] [-c] [-o output]")
        })?;
        let output = match output {
            Some(output) => output,
            None => default_output_path(&input, emit_c)?,
        };
        Ok(Self {
            input,
            output,
            emit_c,
            use_c,
            optimize,
        })
    }
}

struct WasmCli {
    input: PathBuf,
    output: PathBuf,
    optimize: bool,
}

impl WasmCli {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, CompileError> {
        let mut input = None;
        let mut output = None;
        let mut pending_output = false;
        let mut optimize = false;

        for arg in args {
            if pending_output {
                output = Some(PathBuf::from(arg));
                pending_output = false;
                continue;
            }
            match arg.as_str() {
                "-o" | "--output" => pending_output = true,
                "-opt" | "--opt" => optimize = true,
                _ if arg.starts_with('-') => {
                    return Err(CompileError::new(format!("unknown flag: {arg}")));
                }
                _ => {
                    if input.is_some() {
                        return Err(CompileError::new(
                            "expected a single input file and optional -o/--output path",
                        ));
                    }
                    input = Some(PathBuf::from(arg));
                }
            }
        }

        if pending_output {
            return Err(CompileError::new("expected a path after -o/--output"));
        }
        let input = input.ok_or_else(|| {
            CompileError::new("usage: scar wasm <input.scar> [-opt] [-o output.wasm]")
        })?;
        let output = output.unwrap_or_else(|| default_wasm_output_path(&input));
        Ok(Self {
            input,
            output,
            optimize,
        })
    }
}

struct AstCli {
    input: PathBuf,
}

impl AstCli {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, CompileError> {
        let mut input = None;
        for arg in args {
            if arg.starts_with('-') {
                return Err(CompileError::new(format!("unknown flag: {arg}")));
            }
            if input.is_some() {
                return Err(CompileError::new(
                    "expected a single input file after `scar ast`",
                ));
            }
            input = Some(PathBuf::from(arg));
        }
        Ok(Self {
            input: input.ok_or_else(|| CompileError::new("usage: scar ast <input.scar>"))?,
        })
    }
}

struct InspectCli {
    input: PathBuf,
    optimize: bool,
}

impl InspectCli {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, CompileError> {
        let mut input = None;
        let mut optimize = false;

        for arg in args {
            match arg.as_str() {
                "-opt" | "--opt" => optimize = true,
                _ if arg.starts_with('-') => {
                    return Err(CompileError::new(format!("unknown flag: {arg}")));
                }
                _ => {
                    if input.is_some() {
                        return Err(CompileError::new(
                            "expected a single input file after `scar inspect`",
                        ));
                    }
                    input = Some(PathBuf::from(arg));
                }
            }
        }

        Ok(Self {
            input: input
                .ok_or_else(|| CompileError::new("usage: scar inspect <input.scar> [-opt]"))?,
            optimize,
        })
    }
}

struct RunCli {
    input: PathBuf,
}

impl RunCli {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, CompileError> {
        let mut input = None;

        for arg in args {
            if arg.starts_with('-') {
                return Err(CompileError::new(format!("unknown flag: {arg}")));
            }

            if input.is_some() {
                return Err(CompileError::new(
                    "expected a single input file after `scar run`",
                ));
            }

            input = Some(PathBuf::from(arg));
        }

        Ok(Self {
            input: input.ok_or_else(|| CompileError::new("usage: scar run <input.scar>"))?,
        })
    }
}

struct TestCli {
    target: PathBuf,
    output: Option<PathBuf>,
    emit_c: bool,
    optimize: bool,
}

impl TestCli {
    fn parse(args: impl Iterator<Item = String>) -> Result<Self, CompileError> {
        let mut target = None;
        let mut output = None;
        let mut pending_output = false;
        let mut emit_c = false;
        let mut optimize = false;

        for arg in args {
            if pending_output {
                output = Some(PathBuf::from(arg));
                pending_output = false;
                continue;
            }

            match arg.as_str() {
                "-o" | "--output" => pending_output = true,
                "--emit" | "-emit" => emit_c = true,
                "-opt" | "--opt" => optimize = true,
                _ if arg.starts_with('-') => {
                    return Err(CompileError::new(format!("unknown flag: {arg}")));
                }
                _ => {
                    if target.is_some() {
                        return Err(CompileError::new(
                            "expected a single file or directory after `scar test`",
                        ));
                    }
                    target = Some(PathBuf::from(arg));
                }
            }
        }

        if pending_output {
            return Err(CompileError::new("expected a path after -o/--output"));
        }

        Ok(Self {
            target: target.ok_or_else(|| {
                CompileError::new(
                    "usage: scar test <file.scar|directory> [--emit] [-opt] [-o output]",
                )
            })?,
            output,
            emit_c,
            optimize,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompilerKind {
    Tcc,
    Clang,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CompilerSpec {
    kind: CompilerKind,
    opt_flag: &'static str,
}

fn write_output(path: &Path, contents: &str) -> Result<(), CompileError> {
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent).map_err(|error| {
            CompileError::new(format!(
                "failed to create output directory {}: {error}",
                parent.display()
            ))
        })?;
    }
    fs::write(path, contents)
        .map_err(|error| CompileError::new(format!("failed to write {}: {error}", path.display())))
}

fn write_output_bytes(path: &Path, contents: &[u8]) -> Result<(), CompileError> {
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent).map_err(|error| {
            CompileError::new(format!(
                "failed to create output directory {}: {error}",
                parent.display()
            ))
        })?;
    }
    fs::write(path, contents)
        .map_err(|error| CompileError::new(format!("failed to write {}: {error}", path.display())))
}

fn run_build(cli: &BuildCli) -> Result<(), CompileErrors> {
    let program = resolve_entry_program(&cli.input).map_err(CompileErrors::single)?;
    let info = analyze(&program)?;
    emit_program(
        &program,
        &info,
        &cli.input,
        &cli.output,
        cli.emit_c,
        cli.use_c,
        cli.optimize,
    )
    .map_err(CompileErrors::single)?;
    Ok(())
}

fn run_wasm_command(cli: &WasmCli) -> Result<(), CompileErrors> {
    let program = resolve_entry_program(&cli.input).map_err(CompileErrors::single)?;
    let info = analyze(&program)?;
    let bytes = wasm::compile_wasm(&program, &info, cli.optimize).map_err(CompileErrors::single)?;
    write_output_bytes(&cli.output, &bytes).map_err(CompileErrors::single)?;
    Ok(())
}

fn run_ast_command(cli: &AstCli) -> Result<(), CompileErrors> {
    let source = fs::read_to_string(&cli.input).map_err(|error| {
        CompileErrors::single(CompileError::new(format!(
            "failed to read {}: {error}",
            cli.input.display()
        )))
    })?;
    let tokens = lex(&source).map_err(CompileErrors::single)?;
    let program = parse_program(tokens).map_err(CompileErrors::single)?;
    println!("{program:#?}");
    Ok(())
}

fn run_inspect_command(cli: &InspectCli) -> Result<(), CompileErrors> {
    let program = resolve_entry_program(&cli.input).map_err(CompileErrors::single)?;
    let info = analyze(&program)?;
    let ir = clif::compile_ir(&program, &info, cli.optimize).map_err(CompileErrors::single)?;
    print!("{ir}");
    if !ir.ends_with('\n') {
        println!();
    }
    Ok(())
}

fn run_run_command(cli: &RunCli) -> Result<(), CompileErrors> {
    let program = resolve_entry_program(&cli.input).map_err(CompileErrors::single)?;
    let info = analyze(&program)?;
    let binary_path = temporary_run_binary_path(&cli.input);

    let result = (|| {
        emit_program(
            &program,
            &info,
            &cli.input,
            &binary_path,
            false,
            false,
            false,
        )?;
        run_program_binary(&binary_path)
    })();

    let _ = fs::remove_file(&binary_path);
    result.map_err(CompileErrors::single)
}

fn emit_program(
    program: &Program,
    info: &sema::ProgramInfo,
    input: &Path,
    output: &Path,
    emit_c: bool,
    use_c: bool,
    optimize: bool,
) -> Result<(), CompileError> {
    if emit_c || use_c {
        let generated = generate_c(program, info, !optimize)?;
        if emit_c {
            write_output(output, &generated)?;
        } else {
            let c_path = temporary_c_path(input);
            let result = (|| {
                write_output(&c_path, &generated)?;
                compile_c_to_binary(&c_path, output, optimize, &program.link_flags)
            })();
            let _ = fs::remove_file(&c_path);
            result?;
        }
        return Ok(());
    }

    match compile_native_to_binary(program, info, output, optimize) {
        Ok(()) => Ok(()),
        Err(native_error) => {
            let generated = generate_c(program, info, !optimize).map_err(|c_error| {
                CompileError::new(format!(
                    "native backend failed ({native_error}); C fallback failed ({c_error})"
                ))
            })?;
            let c_path = temporary_c_path(input);
            let result = (|| {
                write_output(&c_path, &generated)?;
                compile_c_to_binary(&c_path, output, optimize, &program.link_flags)
            })();
            let _ = fs::remove_file(&c_path);
            result
        }
    }
}

fn compile_native_to_binary(
    program: &Program,
    info: &sema::ProgramInfo,
    output: &Path,
    optimize: bool,
) -> Result<(), CompileError> {
    let artifact = clif::compile_object(program, info, optimize)?;
    let object_path = temporary_object_path(output, artifact.object_extension);
    let runtime_c_path = temporary_runtime_c_path(output);
    let runtime_object_path = temporary_runtime_object_path(output, artifact.object_extension);
    if let Some(parent) = output
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent).map_err(|error| {
            CompileError::new(format!(
                "failed to create output directory {}: {error}",
                parent.display()
            ))
        })?;
    }
    fs::write(&object_path, &artifact.object).map_err(|error| {
        CompileError::new(format!(
            "failed to write {}: {error}",
            object_path.display()
        ))
    })?;
    write_output(&runtime_c_path, clif::runtime_c())?;
    let result = (|| {
        compile_c_to_object(&runtime_c_path, &runtime_object_path, optimize)?;
        link_objects(
            &[object_path.clone(), runtime_object_path.clone()],
            output,
            &program.link_flags,
        )
    })();
    let _ = fs::remove_file(&object_path);
    let _ = fs::remove_file(&runtime_c_path);
    let _ = fs::remove_file(&runtime_object_path);
    result
}

fn compile_c_to_object(
    source_path: &Path,
    object_path: &Path,
    optimize: bool,
) -> Result<(), CompileError> {
    let candidates: &[(&str, bool)] = if cfg!(windows) {
        &[
            ("clang", false),
            ("gcc", false),
            ("cc", false),
            ("cl", true),
        ]
    } else {
        &[("cc", false), ("clang", false), ("gcc", false)]
    };
    let mut last_error = None;
    for (compiler, is_cl) in candidates {
        if !command_available(compiler) {
            continue;
        }
        let mut command = Command::new(compiler);
        if *is_cl {
            command.arg("/c");
            command.arg(source_path);
            command.arg(format!("/Fo{}", object_path.display()));
            command.arg(if optimize { "/O2" } else { "/Od" });
        } else {
            command.arg("-std=c99");
            command.arg(if optimize { "-O2" } else { "-O0" });
            command.arg("-c");
            command.arg(source_path);
            command.arg("-o");
            command.arg(object_path);
        }
        match command.status() {
            Ok(status) if status.success() => return Ok(()),
            Ok(status) => {
                last_error = Some(format!(
                    "{compiler} exited with status {status} while compiling runtime"
                ));
            }
            Err(error) => {
                last_error = Some(format!("failed to run {compiler}: {error}"));
            }
        }
    }
    Err(CompileError::new(last_error.unwrap_or_else(|| {
        "no C toolchain was found for the native runtime".to_string()
    })))
}

fn link_objects(
    object_paths: &[PathBuf],
    output_path: &Path,
    link_flags: &[String],
) -> Result<(), CompileError> {
    let candidates: &[(&str, bool)] = if cfg!(windows) {
        &[
            ("clang", false),
            ("gcc", false),
            ("cc", false),
            ("cl", true),
        ]
    } else {
        &[("cc", false), ("clang", false), ("gcc", false)]
    };
    let mut last_error = None;
    for (compiler, is_cl) in candidates {
        if !command_available(compiler) {
            continue;
        }
        let mut command = Command::new(compiler);
        if *is_cl {
            for object in object_paths {
                command.arg(object);
            }
            command.arg(format!("/Fe:{}", output_path.display()));
            command.arg("/link");
            for flag in link_flags {
                command.arg(flag);
            }
        } else {
            for object in object_paths {
                command.arg(object);
            }
            command.arg("-o");
            command.arg(output_path);
            if cfg!(target_os = "macos") {
                command.arg("-Wl,-w");
            }
            for flag in link_flags {
                command.arg(flag);
            }
        }
        match command.status() {
            Ok(status) if status.success() => return Ok(()),
            Ok(status) => {
                last_error = Some(format!(
                    "{compiler} exited with status {status} while linking {}",
                    output_path.display()
                ));
            }
            Err(error) => {
                last_error = Some(format!("failed to run {compiler}: {error}"));
            }
        }
    }
    Err(CompileError::new(last_error.unwrap_or_else(|| {
        "no system linker or C toolchain was found for native linking".to_string()
    })))
}

fn command_available(command: &str) -> bool {
    Command::new(command)
        .arg("--version")
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
        || Command::new(command)
            .arg("-v")
            .output()
            .map(|output| {
                output.status.success() || !output.stdout.is_empty() || !output.stderr.is_empty()
            })
            .unwrap_or(false)
}

fn run_test_command(cli: &TestCli) -> Result<(), CompileErrors> {
    let files = collect_test_files(&cli.target).map_err(CompileErrors::single)?;
    if files.is_empty() {
        return Err(CompileErrors::single(CompileError::new(format!(
            "no .scar files found at {}",
            cli.target.display()
        ))));
    }
    if cli.output.is_some() && files.len() > 1 {
        return Err(CompileErrors::single(CompileError::new(
            "`scar test -o/--output` only supports a single input file",
        )));
    }

    let mut total_tests = 0usize;
    let mut files_with_tests = 0usize;
    for file in files {
        let count = run_tests_in_file(&file, cli)?;
        if count > 0 {
            files_with_tests += 1;
        }
        total_tests += count;
    }

    if cli.emit_c {
        println!(
            "scar: emitted test C for {} file(s) covering {} tests",
            files_with_tests, total_tests
        );
    } else {
        println!(
            "scar: {} tests passed across {} file(s)",
            total_tests, files_with_tests
        );
    }
    Ok(())
}

fn run_tests_in_file(path: &Path, cli: &TestCli) -> Result<usize, CompileErrors> {
    let program = resolve_entry_program(path).map_err(CompileErrors::single)?;
    let test_count = program.tests.len();
    if test_count == 0 {
        println!("scar: {} (0 tests)", path.display());
        return Ok(0);
    }

    let runner = build_test_program(&program);
    let info = analyze(&runner)?;
    let generated = generate_c(&runner, &info, !cli.optimize).map_err(CompileErrors::single)?;

    if cli.emit_c {
        let output = cli
            .output
            .clone()
            .unwrap_or_else(|| default_test_output_path(path));
        write_output(&output, &generated).map_err(CompileErrors::single)?;
        println!("scar: emitted {} ({} tests)", output.display(), test_count);
        return Ok(test_count);
    }

    let c_path = temporary_test_c_path(path);
    let binary_path = temporary_test_binary_path(path);

    let result = (|| {
        write_output(&c_path, &generated)?;
        compile_c_to_binary(&c_path, &binary_path, cli.optimize, &runner.link_flags)?;
        run_test_binary(&binary_path)?;
        Ok(())
    })();

    let _ = fs::remove_file(&c_path);
    let _ = fs::remove_file(&binary_path);
    result.map_err(CompileErrors::single)?;

    println!("scar: {} ({} tests)", path.display(), test_count);
    Ok(test_count)
}

fn build_test_program(program: &Program) -> Program {
    let mut functions: Vec<Function> = program
        .functions
        .iter()
        .filter(|function| function.name != "main")
        .cloned()
        .collect();
    let mut main_body = Vec::new();

    for (index, test) in program.tests.iter().enumerate() {
        let fn_name = format!("__scar_test_case_{index}");
        functions.push(Function {
            is_pub: false,
            name: fn_name.clone(),
            extern_name: None,
            generic_params: Vec::new(),
            params: Vec::new(),
            return_type: Type::Void,
            body: test.body.clone(),
            line: 0,
            column: 0,
            file_path: None,
        });
        main_body.push(Stmt::Expr {
            line: 0,
            column: 0,
            expr: Expr::Call {
                callee: Box::new(Expr::Path(vec![fn_name])),
                args: Vec::new(),
            },
        });
        main_body.push(Stmt::Expr {
            line: 0,
            column: 0,
            expr: Expr::BuiltinCall {
                name: "puts".to_string(),
                args: vec![Expr::String(format!("[pass] {}", test.name))],
            },
        });
    }

    functions.push(Function {
        is_pub: true,
        name: "main".to_string(),
        extern_name: None,
        generic_params: Vec::new(),
        params: Vec::new(),
        return_type: Type::Void,
        body: main_body,
        line: 0,
        column: 0,
        file_path: None,
    });

    Program {
        module_uses: Vec::new(),
        extern_headers: program.extern_headers.clone(),
        link_flags: program.link_flags.clone(),
        interface_defs: program.interface_defs.clone(),
        type_defs: program.type_defs.clone(),
        typesets: program.typesets.clone(),
        enum_defs: program.enum_defs.clone(),
        functions,
        tests: Vec::new(),
        globals: program.globals.clone(),
    }
}

fn run_test_binary(path: &Path) -> Result<(), CompileError> {
    let status = Command::new(path).status().map_err(|error| {
        CompileError::new(format!(
            "failed to run test binary {}: {error}",
            path.display()
        ))
    })?;
    if status.success() {
        Ok(())
    } else {
        Err(CompileError::new(format!(
            "tests failed in {}",
            path.display()
        )))
    }
}

fn run_program_binary(path: &Path) -> Result<(), CompileError> {
    let status = Command::new(path).status().map_err(|error| {
        CompileError::new(format!(
            "failed to run program binary {}: {error}",
            path.display()
        ))
    })?;
    if status.success() {
        Ok(())
    } else {
        Err(CompileError::new(format!(
            "program exited unsuccessfully: {}",
            path.display()
        )))
    }
}

fn collect_test_files(target: &Path) -> Result<Vec<PathBuf>, CompileError> {
    if target.is_file() {
        return Ok(vec![target.to_path_buf()]);
    }
    if !target.is_dir() {
        return Err(CompileError::new(format!(
            "{} is neither a file nor a directory",
            target.display()
        )));
    }

    let mut files = Vec::new();
    collect_test_files_recursive(target, &mut files)?;
    files.sort();
    Ok(files)
}

fn collect_test_files_recursive(dir: &Path, files: &mut Vec<PathBuf>) -> Result<(), CompileError> {
    for entry in fs::read_dir(dir)
        .map_err(|error| CompileError::new(format!("failed to read {}: {error}", dir.display())))?
    {
        let entry = entry.map_err(|error| {
            CompileError::new(format!("failed to read {}: {error}", dir.display()))
        })?;
        let path = entry.path();
        if path.is_dir() {
            collect_test_files_recursive(&path, files)?;
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("scar") {
            files.push(path);
        }
    }
    Ok(())
}

fn compile_c_to_binary(
    c_path: &Path,
    output_path: &Path,
    optimize: bool,
    link_flags: &[String],
) -> Result<(), CompileError> {
    if let Some(parent) = output_path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent).map_err(|error| {
            CompileError::new(format!(
                "failed to create output directory {}: {error}",
                parent.display()
            ))
        })?;
    }

    let compiler = select_compiler(optimize)?;
    let compiler_name = match compiler.kind {
        CompilerKind::Tcc => "tcc",
        CompilerKind::Clang => "clang",
    };

    let mut use_flag: &str = "-w";

    if compiler_name == "clang" {
        use_flag = "-Wno-everything";
    }

    let status = Command::new(compiler_name)
        .arg("-std=c99")
        .arg(use_flag)
        .arg(compiler.opt_flag)
        .arg(c_path)
        .arg("-o")
        .arg(output_path)
        .args(link_flags)
        .status()
        .map_err(|error| {
            CompileError::new(format!(
                "failed to invoke {compiler_name} for {}: {error}",
                c_path.display()
            ))
        })?;

    if status.success() {
        Ok(())
    } else {
        Err(CompileError::new(format!(
            "{compiler_name} failed to link {}",
            c_path.display()
        )))
    }
}

fn select_compiler(optimize: bool) -> Result<CompilerSpec, CompileError> {
    let has_tcc = command_exists("tcc");
    let has_clang = command_exists("clang");
    choose_compiler(has_tcc, has_clang, optimize)
}

fn choose_compiler(
    has_tcc: bool,
    has_clang: bool,
    optimize: bool,
) -> Result<CompilerSpec, CompileError> {
    if optimize {
        if has_clang {
            return Ok(CompilerSpec {
                kind: CompilerKind::Clang,
                opt_flag: "-O2",
            });
        }
        return Err(CompileError::new(
            "optimized builds require clang, but clang was not found on PATH",
        ));
    }

    if has_tcc {
        return Ok(CompilerSpec {
            kind: CompilerKind::Tcc,
            opt_flag: "-O0",
        });
    }

    if has_clang {
        return Ok(CompilerSpec {
            kind: CompilerKind::Clang,
            opt_flag: "-O0",
        });
    }

    Err(CompileError::new("tcc nor clang were found in PATH"))
}

fn command_exists(command: &str) -> bool {
    Command::new(command).arg("-v").output().is_ok()
}

fn default_output_path(input: &Path, emit_c: bool) -> Result<PathBuf, CompileError> {
    if emit_c {
        return Ok(input.with_extension("c"));
    }

    let stem = input
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or("scar-output");
    let mut output = env::current_dir()
        .map_err(|error| CompileError::new(format!("failed to get current directory: {error}")))?;
    output.push("scar-out");
    output.push(stem);
    if cfg!(windows) {
        output.set_extension("exe");
    } else {
        output.set_extension("");
    }
    Ok(output)
}

fn default_wasm_output_path(input: &Path) -> PathBuf {
    let stem = input
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or("scar-output");
    let mut output = env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    output.push("scar-out");
    output.push(format!("{stem}.wasm"));
    output
}

fn temporary_object_path(output: &Path, extension: &str) -> PathBuf {
    let stem = output
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or("scar-object");
    env::temp_dir().join(format!("scar-{stem}-{}.{}", std::process::id(), extension))
}

fn temporary_runtime_c_path(output: &Path) -> PathBuf {
    let stem = output
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or("scar-runtime");
    env::temp_dir().join(format!("scar-runtime-{stem}-{}.c", std::process::id()))
}

fn temporary_runtime_object_path(output: &Path, extension: &str) -> PathBuf {
    let stem = output
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or("scar-runtime");
    env::temp_dir().join(format!(
        "scar-runtime-{stem}-{}.{}",
        std::process::id(),
        extension
    ))
}

fn temporary_c_path(input: &Path) -> PathBuf {
    let stem = input
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or("scar-output");
    env::temp_dir().join(format!("scar-{stem}-{}.c", std::process::id()))
}

fn temporary_test_c_path(input: &Path) -> PathBuf {
    env::temp_dir().join(format!("scar-test-{}.c", stable_path_hash(input)))
}

fn temporary_test_binary_path(input: &Path) -> PathBuf {
    let mut path = env::temp_dir().join(format!("scar-test-{}", stable_path_hash(input)));
    if cfg!(windows) {
        path.set_extension("exe");
    }
    path
}

fn temporary_run_binary_path(input: &Path) -> PathBuf {
    let stem = input
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or("scar-run");
    let mut path = env::temp_dir().join(format!("scar-run-{stem}-{}", std::process::id()));
    if cfg!(windows) {
        path.set_extension("exe");
    }
    path
}

fn default_test_output_path(input: &Path) -> PathBuf {
    let parent = input.parent().unwrap_or_else(|| Path::new(""));
    let stem = input
        .file_stem()
        .and_then(|value| value.to_str())
        .unwrap_or("scar-test");
    parent.join(format!("{stem}.test.c"))
}

fn stable_path_hash(path: &Path) -> u64 {
    let mut hasher = DefaultHasher::new();
    path.hash(&mut hasher);
    hasher.finish()
}

fn format_compile_error(error: &CompileError, default_path: Option<&Path>) -> String {
    let (path, line, column, message) = resolve_error_site(error, default_path);
    let Some(line) = line else {
        return format!("scar: {message}");
    };
    let Some(column) = column else {
        return format!("scar: {message}");
    };
    let Some(path) = path else {
        return format!("scar: {message} at {line}:{column}");
    };

    let Ok(source) = fs::read_to_string(&path) else {
        return format!("scar: {message}\n --> {}:{line}:{column}", path.display());
    };
    let Some(snippet) = source.lines().nth(line.saturating_sub(1)) else {
        return format!("scar: {message}\n --> {}:{line}:{column}", path.display());
    };

    let line_number = line.to_string();
    let gutter_width = line_number.len();
    let caret_padding = " ".repeat(column.saturating_sub(1));

    format!(
        "scar: {message}\n --> {}:{line}:{column}\n{} |\n{} | {}\n{} | {}^",
        path.display(),
        " ".repeat(gutter_width),
        line_number,
        snippet,
        " ".repeat(gutter_width),
        caret_padding
    )
}

fn resolve_error_site(
    error: &CompileError,
    default_path: Option<&Path>,
) -> (Option<PathBuf>, Option<usize>, Option<usize>, String) {
    let default_or_err_path = error
        .file_path
        .clone()
        .or_else(|| default_path.map(Path::to_path_buf));
    if let Some((line, column)) = error.location() {
        return (
            default_or_err_path,
            Some(line),
            Some(column),
            error.message().to_string(),
        );
    }

    let message = error.message();
    let (path, message) = if let Some(rest) = message.strip_prefix("in ") {
        if let Some((path, tail)) = rest.split_once(": ") {
            (Some(PathBuf::from(path)), tail.to_string())
        } else {
            (default_or_err_path, message.to_string())
        }
    } else {
        (default_or_err_path, message.to_string())
    };

    if let Some((tail, line, column)) = parse_location_suffix(&message) {
        (path, Some(line), Some(column), tail.to_string())
    } else {
        (path, None, None, message)
    }
}

fn parse_location_suffix(message: &str) -> Option<(&str, usize, usize)> {
    let (tail, location) = message.rsplit_once(" at ")?;
    let (line, column) = location.split_once(':')?;
    let line = line.parse().ok()?;
    let column = column.parse().ok()?;
    Some((tail, line, column))
}

#[cfg(test)]
mod tests {
    use super::{
        AstCli, Cli, CompilerKind, InspectCli, RunCli, TestCli, WasmCli, choose_compiler,
        default_output_path, default_wasm_output_path,
    };
    use std::{env, path::Path};

    #[test]
    fn cli_defaults_to_binary_output() {
        let cli = Cli::parse(["build".to_string(), "main.scar".to_string()].into_iter()).unwrap();
        let Cli::Build(cli) = cli else {
            panic!("expected build cli");
        };

        assert!(!cli.emit_c);
        assert!(!cli.use_c);
        assert_eq!(
            cli.output,
            default_output_path(Path::new("main.scar"), false).unwrap()
        );
    }

    #[test]
    fn bare_source_path_still_builds() {
        let cli = Cli::parse(["main.scar".to_string()].into_iter()).unwrap();
        assert!(matches!(cli, Cli::Build(_)));
    }

    #[test]
    fn cli_emit_uses_c_output() {
        let cli = Cli::parse(
            [
                "build".to_string(),
                "--emit".to_string(),
                "main.scar".to_string(),
            ]
            .into_iter(),
        )
        .unwrap();
        let Cli::Build(cli) = cli else {
            panic!("expected build cli");
        };

        assert!(cli.emit_c);
        assert!(cli.use_c);
        assert_eq!(cli.output, Path::new("main.c"));
    }

    #[test]
    fn cli_parses_c_backend_flag() {
        let cli = Cli::parse(
            [
                "build".to_string(),
                "main.scar".to_string(),
                "-c".to_string(),
            ]
            .into_iter(),
        )
        .unwrap();
        let Cli::Build(cli) = cli else {
            panic!("expected build cli");
        };
        assert!(cli.use_c);
        assert!(!cli.emit_c);
    }

    #[test]
    fn cli_parses_wasm_subcommand() {
        let cli = Cli::parse(
            [
                "wasm".to_string(),
                "main.scar".to_string(),
                "-o".to_string(),
                "out.wasm".to_string(),
            ]
            .into_iter(),
        )
        .unwrap();
        let Cli::Wasm(WasmCli {
            input,
            output,
            optimize,
        }) = cli
        else {
            panic!("expected wasm cli");
        };
        assert_eq!(input, Path::new("main.scar"));
        assert_eq!(output, Path::new("out.wasm"));
        assert!(!optimize);
    }

    #[test]
    fn cli_parses_ast_subcommand() {
        let cli = Cli::parse(["ast".to_string(), "main.scar".to_string()].into_iter()).unwrap();
        let Cli::Ast(AstCli { input }) = cli else {
            panic!("expected ast cli");
        };
        assert_eq!(input, Path::new("main.scar"));
    }

    #[test]
    fn cli_parses_inspect_subcommand() {
        let cli = Cli::parse(
            [
                "inspect".to_string(),
                "main.scar".to_string(),
                "-opt".to_string(),
            ]
            .into_iter(),
        )
        .unwrap();
        let Cli::Inspect(InspectCli { input, optimize }) = cli else {
            panic!("expected inspect cli");
        };
        assert_eq!(input, Path::new("main.scar"));
        assert!(optimize);
    }

    #[test]
    fn cli_shows_help_for_unknown_or_missing_commands() {
        assert!(matches!(Cli::parse(std::iter::empty()).unwrap(), Cli::Help));
        assert!(matches!(
            Cli::parse(["nonsense".to_string()].into_iter()).unwrap(),
            Cli::Help
        ));
        assert!(matches!(
            Cli::parse(["help".to_string()].into_iter()).unwrap(),
            Cli::Help
        ));
    }

    #[test]
    fn default_wasm_output_is_under_scar_out() {
        let output = default_wasm_output_path(Path::new("nested/main.scar"));
        assert_eq!(
            output.file_name().and_then(|name| name.to_str()),
            Some("main.wasm")
        );
        assert!(output.starts_with(env::current_dir().unwrap().join("scar-out")));
    }

    #[test]
    fn cli_parses_test_subcommand() {
        let cli = Cli::parse(["test".to_string(), ".".to_string()].into_iter()).unwrap();
        let Cli::Test(TestCli {
            target,
            output,
            emit_c,
            optimize,
        }) = cli
        else {
            panic!("expected test cli");
        };

        assert_eq!(target, Path::new("."));
        assert!(output.is_none());
        assert!(!emit_c);
        assert!(!optimize);
    }

    #[test]
    fn cli_parses_run_subcommand() {
        let cli = Cli::parse(["run".to_string(), "main.scar".to_string()].into_iter()).unwrap();
        let Cli::Run(RunCli { input }) = cli else {
            panic!("expected run cli");
        };

        assert_eq!(input, Path::new("main.scar"));
    }

    #[test]
    fn default_binary_output_uses_invocation_directory() {
        let output = default_output_path(Path::new("nested/main.scar"), false).unwrap();
        let mut expected = env::current_dir().unwrap();
        expected.push("scar-out");
        expected.push(if cfg!(windows) { "main.exe" } else { "main" });

        assert_eq!(output, expected);
    }

    #[test]
    fn optimized_builds_require_clang() {
        let compiler = choose_compiler(true, true, true).unwrap();
        assert_eq!(compiler.kind, CompilerKind::Clang);
        assert_eq!(compiler.opt_flag, "-O2");
    }

    #[test]
    fn dev_builds_prefer_tcc() {
        let compiler = choose_compiler(true, true, false).unwrap();
        assert_eq!(compiler.kind, CompilerKind::Tcc);
        assert_eq!(compiler.opt_flag, "-O0");
    }

    #[test]
    fn dev_builds_fall_back_to_clang() {
        let compiler = choose_compiler(false, true, false).unwrap();
        assert_eq!(compiler.kind, CompilerKind::Clang);
        assert_eq!(compiler.opt_flag, "-O0");
    }

    #[test]
    fn cli_parses_version_subcommand() {
        assert!(matches!(
            Cli::parse(["version".to_string()].into_iter()).unwrap(),
            Cli::Version
        ));
        assert!(matches!(
            Cli::parse(["-V".to_string()].into_iter()).unwrap(),
            Cli::Version
        ));
    }
}
