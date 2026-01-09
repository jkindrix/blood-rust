//! Blood Compiler CLI
//!
//! The main entry point for the Blood compiler.
//!
//! # Usage
//!
//! ```text
//! blood [OPTIONS] <COMMAND>
//!
//! Commands:
//!   lex    Tokenize source and display token stream
//!   parse  Parse source and display AST
//!   check  Type-check source (parsing only in Phase 0)
//!   build  Compile to executable (not yet implemented)
//!   run    Compile and run (not yet implemented)
//!
//! Options:
//!   -v, --verbose  Increase verbosity (can be repeated)
//!   -q, --quiet    Suppress non-error output
//!   --color <WHEN> Control color output [default: auto] [possible values: auto, always, never]
//!   -h, --help     Print help information
//!   -V, --version  Print version information
//! ```

use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Args, Parser, Subcommand, ValueEnum};

use bloodc::diagnostics::DiagnosticEmitter;
use bloodc::{Lexer, TokenKind};

/// The Blood Programming Language Compiler
///
/// Blood is a systems programming language designed for safety-critical domains.
/// It combines content-addressed code, generational memory safety, mutable value
/// semantics, algebraic effects, and multiple dispatch.
#[derive(Parser)]
#[command(name = "blood")]
#[command(author = "Blood Language Team")]
#[command(version)]
#[command(about = "The Blood programming language compiler", long_about = None)]
#[command(propagate_version = true)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// Increase verbosity (can be repeated: -v, -vv, -vvv)
    #[arg(short, long, action = clap::ArgAction::Count, global = true)]
    verbose: u8,

    /// Suppress non-error output
    #[arg(short, long, global = true, conflicts_with = "verbose")]
    quiet: bool,

    /// Control when to use colored output
    #[arg(long, value_enum, default_value_t = ColorChoice::Auto, global = true)]
    color: ColorChoice,
}

#[derive(Subcommand)]
enum Commands {
    /// Tokenize source file and display token stream
    ///
    /// Runs the lexer on the input file and prints each token with its
    /// position, kind, and text (for tokens that carry text).
    Lex(FileArgs),

    /// Parse source file and display AST
    ///
    /// Parses the input file and prints the complete Abstract Syntax Tree
    /// in Rust debug format. Useful for debugging parser issues.
    Parse(FileArgs),

    /// Type-check source file
    ///
    /// Currently only performs parsing (Phase 0). Type checking will be
    /// implemented in Phase 1.
    Check(FileArgs),

    /// Compile source file to executable
    ///
    /// Not yet implemented. Will be available in Phase 1.
    Build(FileArgs),

    /// Compile and run source file
    ///
    /// Not yet implemented. Will be available in Phase 1.
    Run(FileArgs),
}

#[derive(Args)]
struct FileArgs {
    /// Source file to process
    #[arg(value_name = "FILE")]
    file: PathBuf,

    /// Dump additional debug information
    #[arg(short, long)]
    debug: bool,
}

/// When to use colored output
#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum ColorChoice {
    /// Automatically detect if terminal supports colors
    Auto,
    /// Always use colors
    Always,
    /// Never use colors
    Never,
}

impl ColorChoice {
    fn apply(self) {
        match self {
            ColorChoice::Auto => {} // ariadne auto-detects by default
            ColorChoice::Always => {
                // Force colors on
                std::env::set_var("CLICOLOR_FORCE", "1");
            }
            ColorChoice::Never => {
                // Force colors off
                std::env::set_var("NO_COLOR", "1");
            }
        }
    }
}

fn main() -> ExitCode {
    let cli = Cli::parse();

    // Apply color settings
    cli.color.apply();

    // Create verbosity level
    let verbosity = if cli.quiet { 0 } else { cli.verbose + 1 };

    match cli.command {
        Commands::Lex(args) => cmd_lex(&args, verbosity),
        Commands::Parse(args) => cmd_parse(&args, verbosity),
        Commands::Check(args) => cmd_check(&args, verbosity),
        Commands::Build(_) => {
            eprintln!("Error: 'build' is not yet implemented (Phase 1)");
            eprintln!("See ROADMAP.md for implementation timeline.");
            ExitCode::from(1)
        }
        Commands::Run(_) => {
            eprintln!("Error: 'run' is not yet implemented (Phase 1)");
            eprintln!("See ROADMAP.md for implementation timeline.");
            ExitCode::from(1)
        }
    }
}

/// Read source file and return contents
fn read_source(path: &PathBuf) -> Result<String, ExitCode> {
    match fs::read_to_string(path) {
        Ok(s) => Ok(s),
        Err(e) => {
            eprintln!("Error reading file '{}': {}", path.display(), e);
            Err(ExitCode::from(1))
        }
    }
}

/// Lexer command - tokenize and display token stream
fn cmd_lex(args: &FileArgs, verbosity: u8) -> ExitCode {
    let source = match read_source(&args.file) {
        Ok(s) => s,
        Err(code) => return code,
    };

    if verbosity > 1 {
        eprintln!("Lexing file: {}", args.file.display());
        eprintln!("Source length: {} bytes", source.len());
    }

    let lexer = Lexer::new(&source);
    let mut has_errors = false;
    let mut token_count = 0;

    for token in lexer {
        token_count += 1;
        match token.kind {
            TokenKind::Error => {
                has_errors = true;
                eprintln!(
                    "error[E0001]: unexpected character at {}:{}",
                    token.span.start_line, token.span.start_col
                );
            }
            TokenKind::UnclosedBlockComment => {
                has_errors = true;
                eprintln!(
                    "error[E0002]: unclosed block comment starting at {}:{}",
                    token.span.start_line, token.span.start_col
                );
            }
            TokenKind::Eof => {
                if args.debug {
                    println!("{:4}:{:<3} {:?}", token.span.start_line, token.span.start_col, token.kind);
                }
            }
            _ => {
                let text = if token.kind.has_text() {
                    format!(" '{}'", &source[token.span.start..token.span.end])
                } else {
                    String::new()
                };
                println!(
                    "{:4}:{:<3} {:?}{}",
                    token.span.start_line, token.span.start_col, token.kind, text
                );
            }
        }
    }

    if verbosity > 0 && !has_errors {
        eprintln!("Lexed {} tokens successfully.", token_count);
    }

    if has_errors {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}

/// Parse command - parse and display AST
fn cmd_parse(args: &FileArgs, verbosity: u8) -> ExitCode {
    let source = match read_source(&args.file) {
        Ok(s) => s,
        Err(code) => return code,
    };

    if verbosity > 1 {
        eprintln!("Parsing file: {}", args.file.display());
    }

    let mut parser = bloodc::Parser::new(&source);
    let result = parser.parse_program();

    let path_str = args.file.to_string_lossy();
    let emitter = DiagnosticEmitter::new(&path_str, &source);

    match result {
        Ok(program) => {
            println!("{:#?}", program);
            if verbosity > 0 {
                eprintln!(
                    "Parsed {} declarations successfully.",
                    program.declarations.len()
                );
            }
            ExitCode::SUCCESS
        }
        Err(errors) => {
            for error in &errors {
                emitter.emit(error);
            }
            eprintln!("Parsing failed with {} error(s).", errors.len());
            ExitCode::from(1)
        }
    }
}

/// Check command - type-check source
fn cmd_check(args: &FileArgs, verbosity: u8) -> ExitCode {
    let source = match read_source(&args.file) {
        Ok(s) => s,
        Err(code) => return code,
    };

    if verbosity > 1 {
        eprintln!("Checking file: {}", args.file.display());
    }

    let mut parser = bloodc::Parser::new(&source);
    let result = parser.parse_program();

    let path_str = args.file.to_string_lossy();
    let emitter = DiagnosticEmitter::new(&path_str, &source);

    match result {
        Ok(program) => {
            if verbosity > 0 {
                eprintln!(
                    "Parsed {} declarations.",
                    program.declarations.len()
                );
            }
            // Type checking not yet implemented
            println!("info: Parsing successful.");
            println!("info: Type checking not yet implemented (Phase 0).");
            println!("hint: See ROADMAP.md for Phase 1 implementation plans.");
            ExitCode::SUCCESS
        }
        Err(errors) => {
            for error in &errors {
                emitter.emit(error);
            }
            eprintln!("Checking failed with {} error(s).", errors.len());
            ExitCode::from(1)
        }
    }
}
