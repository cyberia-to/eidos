// repl — interactive read-eval-print loop
// Commands: def/theorem/axiom declarations, :check, :eval, :env, :help, :quit

use std::io::{self, BufRead, Write};

use cyber_eidos::{
    elab::{ElabState, elab_expr},
    env::Env,
    reduce::nf,
    stdlib::std_env,
    surface::{
        check::{check_file, DeclKind},
        lexer::lex,
        parser::parse_file,
    },
};

use crate::pretty;

// ── Public entry point ────────────────────────────────────────────────────────

pub fn run() {
    let mut env = std_env();
    let mut st  = ElabState::new();
    st.add_stdlib();

    let stdin  = io::stdin();
    let stdout = io::stdout();

    print!("{}", crate::banner());
    println!("  {}", crate::dim("interactive · :help for commands · :quit to exit"));

    let prompt = format!("{}{} ", crate::cyan("eidos"), crate::dim("›"));
    let mut buf = String::new();
    loop {
        // Print prompt
        {
            let mut out = stdout.lock();
            write!(out, "{prompt}").unwrap();
            out.flush().unwrap();
        }

        buf.clear();
        match stdin.lock().read_line(&mut buf) {
            Ok(0) | Err(_) => break,  // EOF
            Ok(_) => {}
        }

        let line = buf.trim();
        if line.is_empty() || line.starts_with("--") { continue; }

        if line.starts_with(':') {
            handle_command(line, &env, &mut st);
            continue;
        }

        // Try to parse and process as a declaration or #check
        process_input(line, &mut env, &mut st);
    }
    println!();
}

// ── Command dispatch ──────────────────────────────────────────────────────────

fn handle_command(line: &str, env: &Env, st: &mut ElabState) {
    let (cmd, rest) = line[1..].split_once(char::is_whitespace)
        .unwrap_or((&line[1..], ""));
    let rest = rest.trim();

    match cmd {
        "quit" | "q" | "exit" => {
            println!("bye.");
            std::process::exit(0);
        }
        "help" | "h" => print_help(),
        "check" | "c" => cmd_check_expr(rest, env, st),
        "eval"  | "e" => cmd_eval_expr(rest, env, st),
        "env"         => cmd_show_env(env, st),
        "reset"       => {
            println!("(environment reset)");
            // Can't reassign env/st here without &mut — user can restart
            println!("hint: restart eidos to reset the environment");
        }
        other => eprintln!("unknown command :{other}  (type :help for help)"),
    }
}

fn print_help() {
    println!("commands:");
    println!("  :check <expr>     show the type of an expression");
    println!("  :eval  <expr>     evaluate an expression to normal form");
    println!("  :env              list all definitions in scope");
    println!("  :quit             exit the REPL");
    println!();
    println!("declarations:");
    println!("  def name (params) : ty := body");
    println!("  theorem name (params) : ty := proof");
    println!("  theorem name (params) : ty := by {{ tac1; tac2 }}");
    println!("  axiom name : ty");
    println!();
    println!("tactics (in by {{ }} blocks):");
    println!("  intro x y ...    apply f    exact e    rfl    assumption");
    println!("  induction x      cases x    omega      simp   contradiction");
    println!("  have h : T := e  rewrite [h]  rewrite [← h]  sorry");
}

fn cmd_check_expr(src: &str, env: &Env, st: &mut ElabState) {
    if src.is_empty() {
        eprintln!(":check requires an expression");
        return;
    }
    match elaborate_expr(src, env, st) {
        Ok((_, ty)) => println!("  {} {}", crate::dim(":"), crate::cyan(&pretty::pp(&ty))),
        Err(e) => eprintln!("  {}: {e}", crate::red("error")),
    }
}

fn cmd_eval_expr(src: &str, env: &Env, st: &mut ElabState) {
    if src.is_empty() {
        eprintln!(":eval requires an expression");
        return;
    }
    match elaborate_expr(src, env, st) {
        Ok((term, ty)) => {
            let ctx = vec![];
            let nf_term = nf(env, &ctx, term);
            let nf_ty   = nf(env, &ctx, ty);
            println!(
                "  {} {} {}",
                crate::green(&pretty::pp(&nf_term)),
                crate::dim(":"),
                crate::cyan(&pretty::pp(&nf_ty)),
            );
        }
        Err(e) => eprintln!("  {}: {e}", crate::red("error")),
    }
}

fn cmd_show_env(_env: &Env, st: &ElabState) {
    if st.globals.is_empty() {
        println!("(no definitions)");
    } else {
        let mut names: Vec<&str> = st.globals.keys().map(String::as_str).collect();
        names.sort_unstable();
        for name in names {
            if let Some((_, ty)) = st.globals.get(name) {
                println!("  {} {} {}", crate::bold(name), crate::dim(":"), crate::dim(&pretty::pp(ty)));
            }
        }
    }
}

// ── Declaration processing ────────────────────────────────────────────────────

fn process_input(src: &str, env: &mut Env, st: &mut ElabState) {
    // Lex and parse
    let tokens = match lex(src) {
        Ok(t)  => t,
        Err(e) => { eprintln!("lex error: {e}"); return; }
    };
    let decls = match parse_file(&tokens) {
        Ok(d)  => d,
        Err(e) => { eprintln!("parse error: {e}"); return; }
    };

    if decls.is_empty() {
        // Try as an expression
        cmd_eval_expr(src, env, st);
        return;
    }

    match check_file(&decls, st, env) {
        Ok(results) => {
            for r in results {
                let ty = crate::dim(&pretty::pp(&r.ty));
                let nm = crate::bold(&r.name);
                match r.kind {
                    DeclKind::Def       => println!("  {} {} {} {}", crate::dim("def      "), nm, crate::dim(":"), ty),
                    DeclKind::Theorem   => println!("  {} {} {} {}", crate::green("proved   "), nm, crate::dim(":"), ty),
                    DeclKind::Axiom     => println!("  {} {} {} {}", crate::yellow("axiom    "), nm, crate::dim(":"), ty),
                    DeclKind::Inductive => println!("  {} {}", crate::magenta("inductive"), nm),
                }
            }
        }
        Err((name, err)) => eprintln!("  {}: in '{name}': {err}", crate::red("error")),
    }
}

// ── Expression helper ─────────────────────────────────────────────────────────

fn elaborate_expr(
    src: &str,
    env: &Env,
    st: &mut ElabState,
) -> Result<(cyber_eidos::Term, cyber_eidos::Term), String> {
    // Try the surface parser first
    let tokens = lex(src).map_err(|e| format!("lex: {e}"))?;
    use cyber_eidos::surface::parser::parse_expr_tokens;
    let expr = parse_expr_tokens(&tokens).map_err(|e| format!("parse: {e}"))?;
    let (term, ty) = elab_expr(st, env, &expr)
        .map_err(|e| format!("elab: {e:?}"))?;
    let ctx = vec![];
    let ty_nf = nf(env, &ctx, st.mctx.zonk(&ty));
    Ok((term, ty_nf))
}
