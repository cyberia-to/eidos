//! Closed-term checking in the Nat/Bool/Eq/Pos fragment, without admissions.
//! The frontend constructs terms; a fresh, fixed kernel environment rechecks
//! each declaration before it can become a dependency of another declaration.

use super::{DeclKind, DeclResult, SurfaceDecl, Token, check_file, lex, parse_file};
use crate::{elab::ElabState, env::Env, kernel, reduce::nf, stdlib, term::Term};
use std::{
    collections::HashSet,
    path::{Path, PathBuf},
};

/// A successfully checked module, including its transitive imported declarations.
#[derive(Debug)]
pub struct CheckedModule {
    pub state: ElabState,
    pub declarations: Vec<DeclResult>,
    /// Canonical paths in dependency order. Source-only checks have no files.
    pub files: Vec<PathBuf>,
}

/// Check source without file imports. No caller-supplied environment is trusted.
pub fn check_strict_source(source: &str) -> Result<CheckedModule, String> {
    let mut checker = StrictChecker::new()?;
    checker.source(source, None)?;
    Ok(checker.module)
}

/// Check a file and all imports with the same strict policy; cycles are errors.
pub fn check_strict_path(path: &Path) -> Result<CheckedModule, String> {
    let mut checker = StrictChecker::new()?;
    checker.path(path)?;
    Ok(checker.module)
}

struct StrictChecker {
    module: CheckedModule,
    env: Env,
    names: HashSet<String>,
    active: HashSet<PathBuf>,
    loaded: HashSet<PathBuf>,
}

impl StrictChecker {
    fn new() -> Result<Self, String> {
        let env = fragment_env();
        let mut state = ElabState::new();
        state.add_stdlib();
        // Reserve even unsupported standard names: modules cannot quietly
        // replace a bootstrap placeholder with a different meaning.
        let names = state.globals.keys().cloned().collect();
        const PRELUDE: &[&str] = &[
            "Pos",
            "Pos.one",
            "Pos.bit0",
            "Pos.bit1",
            "Pos.succ",
            "Pos.add",
            "Nat",
            "Bool",
            "Eq",
            "Eq.refl",
            "Nat.zero",
            "Nat.succ",
            "Nat.add",
            "Nat.mul",
            "Nat.sub",
            "Bool.false",
            "Bool.true",
            "false",
            "true",
        ];
        state
            .globals
            .retain(|name, _| PRELUDE.contains(&name.as_str()));
        for (name, (body, ty)) in &state.globals {
            recheck(&env, body, ty, false).map_err(|e| format!("prelude {name}: {e}"))?;
        }
        Ok(Self {
            module: CheckedModule {
                state,
                declarations: vec![],
                files: vec![],
            },
            env,
            names,
            active: HashSet::new(),
            loaded: HashSet::new(),
        })
    }

    fn path(&mut self, path: &Path) -> Result<(), String> {
        let path = path
            .canonicalize()
            .map_err(|e| format!("{}: {e}", path.display()))?;
        if self.active.contains(&path) {
            return Err(format!("import cycle: {}", path.display()));
        }
        if self.loaded.contains(&path) {
            return Ok(());
        }
        if self.active.len() >= 64 {
            return Err("import depth exceeds 64".into());
        }
        self.active.insert(path.clone());
        let source = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
        self.source(&source, path.parent())
            .map_err(|e| format!("{}: {e}", path.display()))?;
        self.active.remove(&path);
        self.loaded.insert(path.clone());
        self.module.files.push(path);
        Ok(())
    }

    fn source(&mut self, source: &str, base: Option<&Path>) -> Result<(), String> {
        let tokens = lex(source)?;
        for token in &tokens {
            if matches!(
                token,
                Token::KwAxiom | Token::KwSorry | Token::KwInductive | Token::Hash
            ) {
                return Err(format!("strict checking excludes {token:?}"));
            }
        }
        for decl in parse_file(&tokens)? {
            let name = match &decl {
                SurfaceDecl::Import { path } => {
                    let dir = base.ok_or("imports require check_strict_path")?;
                    self.path(&dir.join(path))?;
                    continue;
                }
                SurfaceDecl::Def { name, .. } | SurfaceDecl::Theorem { name, .. } => name.clone(),
                _ => return Err("declaration outside strict fragment".into()),
            };
            if !self.names.insert(name.clone()) {
                return Err(format!("duplicate or reserved declaration: {name}"));
            }
            let mut results = check_file(&[decl], &mut self.module.state, &mut self.env)
                .map_err(|(name, e)| format!("{name}: {e}"))?;
            let result = results.pop().ok_or("missing declaration result")?;
            let (body, ty) = self.module.state.globals.get(&name).ok_or("missing body")?;
            recheck(&fragment_env(), body, ty, result.kind == DeclKind::Theorem)
                .map_err(|e| format!("{name}: {e}"))?;
            self.module.declarations.push(result);
        }
        Ok(())
    }
}

fn fragment_env() -> Env {
    let mut env = Env::new();
    stdlib::nat::declare_nat(&mut env);
    stdlib::binary::declare(&mut env);
    stdlib::bool::declare_bool(&mut env);
    stdlib::prop::declare_eq(&mut env);
    env
}

fn recheck(env: &Env, body: &Term, ty: &Term, theorem: bool) -> Result<(), String> {
    clean(body)?;
    clean(ty)?;
    let ctx = vec![];
    let sort = kernel::infer(env, &ctx, ty).map_err(|e| format!("type: {e:?}"))?;
    let sort = nf(env, &ctx, sort);
    if !matches!(sort, Term::Sort(_)) {
        return Err("declared type is not a type".into());
    }
    if theorem && sort != Term::Sort(0) {
        return Err("theorem is not a proposition".into());
    }
    kernel::check(env, &ctx, body, ty).map_err(|e| format!("closed term: {e:?}"))
}

fn clean(t: &Term) -> Result<(), String> {
    match t {
        Term::Const(_) | Term::Meta(_) => return Err("constant or unresolved metavariable".into()),
        Term::Var(_) | Term::Sort(_) => {}
        Term::Pi(a, b) | Term::Lam(a, b) | Term::App(a, b) => {
            clean(a)?;
            clean(b)?;
        }
        Term::Let(a, b, c) | Term::EqSubst(a, b, c) => {
            clean(a)?;
            clean(b)?;
            clean(c)?;
        }
        Term::Ind(id, xs) | Term::Ctor(id, _, xs) => {
            allowed_ind(*id)?;
            for x in xs {
                clean(x)?;
            }
        }
        Term::Elim(id, motive, cases, target) => {
            allowed_ind(*id)?;
            clean(motive)?;
            clean(target)?;
            for case in cases {
                clean(case)?;
            }
        }
    }
    Ok(())
}

fn allowed_ind(id: u64) -> Result<(), String> {
    if [
        stdlib::NAT_ID,
        stdlib::BOOL_ID,
        stdlib::EQ_ID,
        stdlib::binary::POS_ID,
    ]
    .contains(&id)
    {
        Ok(())
    } else {
        Err(format!("inductive outside strict fragment: {id}"))
    }
}
