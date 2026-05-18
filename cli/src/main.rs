// eidos CLI
// spec: specs/interaction.md § query commands

mod pretty;
mod parser;
mod repl;

use std::{env, fs, process};
use cyber_eidos::{
    elab::{ElabState, elab_expr},
    reduce::nf,
    stdlib::std_env,
    surface::{check_file, lex, parse_file, DeclKind},
};

fn usage() -> ! {
    eprintln!("eidos <command> [args]");
    eprintln!();
    eprintln!("commands:");
    eprintln!("  repl              interactive proof assistant");
    eprintln!("  eval   <expr>     reduce expression to normal form and show its type");
    eprintln!("  check  <file.ei>  elaborate and kernel-check all declarations");
    eprintln!("  search <type>     query cybergraph for existing proofs");
    eprintln!("  verify <axon>     fetch and verify a proof certificate");
    process::exit(1)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 { usage(); }

    match args[1].as_str() {
        "repl" | "r"  => repl::run(),
        "eval"        => cmd_eval(&args[2..]),
        "check"       => cmd_check(&args[2..]),
        "search"      => cmd_search(&args[2..]),
        "verify"      => cmd_verify(&args[2..]),
        _             => usage(),
    }
}

// ── eval ─────────────────────────────────────────────────────────────────────

fn cmd_eval(args: &[String]) {
    let Some(expr_str) = args.first() else {
        eprintln!("eval: missing expression");
        eprintln!("usage: eidos eval <expr>");
        process::exit(1)
    };

    let expr = match parser::parse(expr_str) {
        Ok(e)  => e,
        Err(e) => { eprintln!("parse error: {}", e); process::exit(1) }
    };

    let env = std_env();
    let mut st = ElabState::new();
    st.add_stdlib();

    match elab_expr(&mut st, &env, &expr) {
        Ok((term, ty)) => {
            let ctx = vec![];
            let term_nf = nf(&env, &ctx, term);
            let ty_nf   = nf(&env, &ctx, st.mctx.zonk(&ty));
            println!("{} : {}", pretty::pp(&term_nf), pretty::pp(&ty_nf));
        }
        Err(e) => {
            eprintln!("elaboration error: {:?}", e);
            process::exit(1)
        }
    }
}

// ── check ────────────────────────────────────────────────────────────────────

fn cmd_check(args: &[String]) {
    let Some(path) = args.first() else {
        eprintln!("check: missing file");
        eprintln!("usage: eidos check <file.ei>");
        process::exit(1)
    };

    let src = match fs::read_to_string(path) {
        Ok(s)  => s,
        Err(e) => { eprintln!("check: cannot read '{path}': {e}"); process::exit(1) }
    };

    let tokens = match lex(&src) {
        Ok(t)  => t,
        Err(e) => { eprintln!("lex error: {e}"); process::exit(1) }
    };
    let decls = match parse_file(&tokens) {
        Ok(d)  => d,
        Err(e) => { eprintln!("parse error: {e}"); process::exit(1) }
    };

    let mut env = std_env();
    let mut st  = ElabState::new();
    st.add_stdlib();

    match check_file(&decls, &mut st, &mut env) {
        Ok(results) => {
            for r in &results {
                match r.kind {
                    DeclKind::Def       => println!("def {}  : {}", r.name, pretty::pp(&r.ty)),
                    DeclKind::Theorem   => println!("proved  : {} : {}", r.name, pretty::pp(&r.ty)),
                    DeclKind::Axiom     => println!("axiom   : {} : {}", r.name, pretty::pp(&r.ty)),
                    DeclKind::Inductive => println!("inductive: {}", r.name),
                }
            }
            println!("ok — {} declaration(s) checked", results.len());
        }
        Err((name, err)) => {
            eprintln!("error in '{name}': {err}");
            process::exit(1)
        }
    }
}

// ── search ───────────────────────────────────────────────────────────────────

fn cmd_search(args: &[String]) {
    let Some(ty_str) = args.first() else {
        eprintln!("search: missing type");
        eprintln!("usage: eidos search <type>");
        process::exit(1)
    };
    eprintln!("search: {ty_str} (cybergraph query not yet implemented)");
    process::exit(1)
}

// ── verify ───────────────────────────────────────────────────────────────────

fn cmd_verify(args: &[String]) {
    let Some(axon) = args.first() else {
        eprintln!("verify: missing axon");
        eprintln!("usage: eidos verify <axon-hash>");
        process::exit(1)
    };
    eprintln!("verify: {axon} (zheng verifier not yet implemented)");
    process::exit(1)
}
