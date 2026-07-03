// eidos CLI
// spec: specs/interaction.md § query commands

mod pretty;
mod parser;
mod repl;

use std::io::IsTerminal;
use std::{env, fs, process};
use cyber_eidos::{
    elab::{ElabState, elab_expr},
    reduce::nf,
    stdlib::std_env,
    surface::{check_file, lex, parse_file, DeclKind},
};

// ── style ────────────────────────────────────────────────────────────────────
// ANSI only when stdout is a terminal — piped output stays clean.

fn tty() -> bool {
    std::io::stdout().is_terminal()
}
fn paint(code: &str, s: &str) -> String {
    if tty() { format!("\x1b[{code}m{s}\x1b[0m") } else { s.to_string() }
}
fn dim(s: &str) -> String {
    paint("90", s)
}
fn cyan(s: &str) -> String {
    paint("36", s)
}
fn green(s: &str) -> String {
    paint("32", s)
}
fn yellow(s: &str) -> String {
    paint("33", s)
}
fn magenta(s: &str) -> String {
    paint("35", s)
}
fn bold(s: &str) -> String {
    paint("1", s)
}
fn red(s: &str) -> String {
    paint("31", s)
}

const LOGO: &str = "\
\x1b[31m███████╗██╗██████╗  ██████╗ ███████╗\x1b[0m
\x1b[33m██╔════╝██║██╔══██╗██╔═══██╗██╔════╝\x1b[0m
\x1b[32m█████╗  ██║██║  ██║██║   ██║███████╗\x1b[0m
\x1b[36m██╔══╝  ██║██║  ██║██║   ██║╚════██║\x1b[0m
\x1b[34m███████╗██║██████╔╝╚██████╔╝███████║\x1b[0m
\x1b[35m╚══════╝╚═╝╚═════╝  ╚═════╝ ╚══════╝\x1b[0m";

/// The rainbow wordmark + tagline + the CIC parameters. Empty when not a tty.
pub fn banner() -> String {
    if !tty() {
        return String::new();
    }
    format!(
        "{LOGO}\n{tag}\n{params}\n",
        tag = paint("37", "    the form of truth"),
        params = dim(
            "\n    Calculus of Inductive Constructions\n    \
             proofs are programs · types are propositions\n    \
             Π · inductives · universes · kernel-checked\n"
        ),
    )
}

fn help_lines() -> String {
    let rows = [
        ("repl", "interactive proof assistant"),
        ("eval <expr>", "reduce to normal form, show its type"),
        ("check <file.ei>", "elaborate + kernel-check all declarations"),
        ("search <type>", "query cybergraph for existing proofs"),
        ("verify <axon>", "fetch and verify a proof certificate"),
    ];
    let w = rows.iter().map(|(c, _)| c.len()).max().unwrap_or(0);
    let mut s = format!("{}\n", dim("commands"));
    for (cmd, desc) in rows {
        s.push_str(&format!("  {}   {}\n", bold(&format!("{cmd:<w$}")), dim(desc)));
    }
    s
}

fn usage() -> ! {
    eprint!("{}", banner());
    eprint!("{}", help_lines());
    process::exit(1)
}

fn main() {
    let args: Vec<String> = env::args().collect();

    match args.get(1).map(String::as_str) {
        Some("repl") | Some("r") => repl::run(),
        Some("eval") => cmd_eval(&args[2..]),
        Some("check") => cmd_check(&args[2..]),
        Some("search") => cmd_search(&args[2..]),
        Some("verify") => cmd_verify(&args[2..]),
        Some("help") | Some("--help") | Some("-h") => {
            print!("{}", banner());
            print!("{}", help_lines());
        }
        _ => usage(),
    }
}

/// Print an error and exit non-zero.
fn die(kind: &str, msg: impl std::fmt::Display) -> ! {
    eprintln!("  {}: {msg}", red(kind));
    process::exit(1)
}

// ── eval ─────────────────────────────────────────────────────────────────────

fn cmd_eval(args: &[String]) {
    let Some(expr_str) = args.first() else {
        die("eval", "missing expression — usage: eidos eval <expr>");
    };

    let expr = match parser::parse(expr_str) {
        Ok(e) => e,
        Err(e) => die("parse error", e),
    };

    let env = std_env();
    let mut st = ElabState::new();
    st.add_stdlib();

    match elab_expr(&mut st, &env, &expr) {
        Ok((term, ty)) => {
            let ctx = vec![];
            let term_nf = nf(&env, &ctx, term);
            let ty_nf = nf(&env, &ctx, st.mctx.zonk(&ty));
            println!("  {} {} {}", green(&pretty::pp(&term_nf)), dim(":"), cyan(&pretty::pp(&ty_nf)));
        }
        Err(e) => die("elaboration error", format!("{e:?}")),
    }
}

// ── check ────────────────────────────────────────────────────────────────────

fn cmd_check(args: &[String]) {
    let Some(path) = args.first() else {
        die("check", "missing file — usage: eidos check <file.ei>");
    };

    let src = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => die("check", format!("cannot read '{path}': {e}")),
    };

    let tokens = match lex(&src) {
        Ok(t) => t,
        Err(e) => die("lex error", e),
    };
    let decls = match parse_file(&tokens) {
        Ok(d) => d,
        Err(e) => die("parse error", e),
    };

    let mut env = std_env();
    let mut st = ElabState::new();
    st.add_stdlib();

    match check_file(&decls, &mut st, &mut env) {
        Ok(results) => {
            for r in &results {
                let ty = dim(&pretty::pp(&r.ty));
                match r.kind {
                    DeclKind::Def => {
                        println!("  {} {} {} {}", dim("def      "), bold(&r.name), dim(":"), ty)
                    }
                    DeclKind::Theorem => {
                        println!("  {} {} {} {}", green("proved   "), bold(&r.name), dim(":"), ty)
                    }
                    DeclKind::Axiom => {
                        println!("  {} {} {} {}", yellow("axiom    "), bold(&r.name), dim(":"), ty)
                    }
                    DeclKind::Inductive => {
                        println!("  {} {}", magenta("inductive"), bold(&r.name))
                    }
                }
            }
            println!(
                "  {} {}",
                green("✓"),
                dim(&format!("{} declaration(s) checked", results.len())),
            );
        }
        Err((name, err)) => die("error", format!("in '{name}': {err}")),
    }
}

// ── search ───────────────────────────────────────────────────────────────────

fn cmd_search(args: &[String]) {
    let Some(ty_str) = args.first() else {
        die("search", "missing type — usage: eidos search <type>");
    };
    eprintln!("  {} {ty_str} {}", dim("search"), dim("(cybergraph query not yet implemented)"));
    process::exit(1)
}

// ── verify ───────────────────────────────────────────────────────────────────

fn cmd_verify(args: &[String]) {
    let Some(axon) = args.first() else {
        die("verify", "missing axon — usage: eidos verify <axon-hash>");
    };
    eprintln!("  {} {axon} {}", dim("verify"), dim("(zheng verifier not yet implemented)"));
    process::exit(1)
}
