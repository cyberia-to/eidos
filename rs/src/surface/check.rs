// check — elaborate and kernel-verify a sequence of surface declarations
// spec: specs/surface.md § declaration elaboration

use std::path::Path;
use crate::{
    env::{ConstDecl, Env},
    elab::{
        ast::{Binder, Decl, Expr},
        core::{elab_expr, fold_lam, fold_pi, push_params, ElabState},
        decl::{elab_decl, fnv_hash},
        ElabError,
    },
    kernel,
    term::Term,
};
use super::{
    parser::{Proof, SurfaceDecl},
    tactic_runner::{run_proof, RunError},
};

// ── Error ─────────────────────────────────────────────────────────────────────

#[derive(Debug)]
pub enum CheckError {
    Elab(ElabError),
    Kernel(kernel::Error),
    Tactic(RunError),
    ParseError(String),
    Sorry(String),
}

impl std::fmt::Display for CheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CheckError::Elab(e)        => write!(f, "elaboration error: {e:?}"),
            CheckError::Kernel(e)      => write!(f, "kernel error: {e:?}"),
            CheckError::Tactic(e)      => write!(f, "tactic error: {e:?}"),
            CheckError::ParseError(s)  => write!(f, "parse error: {s}"),
            CheckError::Sorry(s)       => write!(f, "sorry: {s}"),
        }
    }
}

impl From<ElabError> for CheckError {
    fn from(e: ElabError) -> Self { CheckError::Elab(e) }
}
impl From<kernel::Error> for CheckError {
    fn from(e: kernel::Error) -> Self { CheckError::Kernel(e) }
}
impl From<RunError> for CheckError {
    fn from(e: RunError) -> Self { CheckError::Tactic(e) }
}

// ── Result record ─────────────────────────────────────────────────────────────

/// Result of checking one declaration.
#[derive(Debug)]
pub struct DeclResult {
    pub name: String,
    pub kind: DeclKind,
    pub ty:   Term,
}

#[derive(Debug, PartialEq)]
pub enum DeclKind { Def, Theorem, Axiom, Inductive }

// ── Public API ────────────────────────────────────────────────────────────────

/// Check all declarations in order. Returns a list of results or the first error.
pub fn check_file(
    decls: &[SurfaceDecl],
    st: &mut ElabState,
    env: &mut Env,
) -> Result<Vec<DeclResult>, (String, CheckError)> {
    check_file_with_base(decls, st, env, None)
}

/// Check declarations with a base directory for resolving imports.
pub fn check_file_with_base(
    decls: &[SurfaceDecl],
    st: &mut ElabState,
    env: &mut Env,
    base_dir: Option<&Path>,
) -> Result<Vec<DeclResult>, (String, CheckError)> {
    let mut results = Vec::new();
    for decl in decls {
        match check_one_with_base(decl, st, env, base_dir) {
            Ok(r)  => results.push(r),
            Err(e) => {
                let name = decl_name(decl).unwrap_or("(unknown)").to_string();
                return Err((name, e));
            }
        }
    }
    Ok(results)
}

/// Read a .ei file from disk and check it, resolving imports relative to the file's directory.
pub fn check_path(
    path: &Path,
    st: &mut ElabState,
    env: &mut Env,
) -> Result<Vec<DeclResult>, (String, CheckError)> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| (path.display().to_string(), CheckError::ParseError(e.to_string())))?;
    let toks = super::lex(&src)
        .map_err(|e| ("lex".to_string(), CheckError::ParseError(e)))?;
    let decls = super::parse_file(&toks)
        .map_err(|e| ("parse".to_string(), CheckError::ParseError(e)))?;
    check_file_with_base(&decls, st, env, path.parent())
}

fn check_one(decl: &SurfaceDecl, st: &mut ElabState, env: &mut Env) -> Result<DeclResult, CheckError> {
    check_one_with_base(decl, st, env, None)
}

fn check_one_with_base(decl: &SurfaceDecl, st: &mut ElabState, env: &mut Env, base_dir: Option<&Path>) -> Result<DeclResult, CheckError> {
    match decl {
        SurfaceDecl::Def { name, params, ty, body } => {
            let (closed_ty, closed_body) = elab_def_term(st, env, params, ty, body)?;
            st.globals.insert(name.clone(), (closed_body.clone(), closed_ty.clone()));
            Ok(DeclResult { name: name.clone(), kind: DeclKind::Def, ty: closed_ty })
        }

        SurfaceDecl::Theorem { name, params, ty, proof } => {
            check_theorem(st, env, name, params, ty, proof)
        }

        SurfaceDecl::Axiom { name, params, ty } => {
            let n_before = st.locals.len();
            let param_types = push_params(st, env, params).map_err(CheckError::Elab)?;
            let (ty_term, _) = elab_expr(st, env, ty).map_err(CheckError::Elab)?;
            let ty_z = st.mctx.zonk(&ty_term);
            kernel::infer(env, &st.ctx(), &ty_z)?;
            let n_params = st.locals.len() - n_before;
            for _ in 0..n_params { st.pop(); }
            let closed_ty = fold_pi(&param_types, ty_z);
            let id = fnv_hash(name.as_bytes());
            env.insert_const(id, ConstDecl { ty: closed_ty.clone(), body: None });
            st.globals.insert(name.clone(), (Term::Const(id), closed_ty.clone()));
            Ok(DeclResult { name: name.clone(), kind: DeclKind::Axiom, ty: closed_ty })
        }

        SurfaceDecl::Inductive { name, params, sort, ctors } => {
            // Convert to elab::ast::Decl::Inductive and delegate
            let ast_ctors: Vec<(String, Box<Expr>)> = ctors.iter()
                .map(|(n, e)| (n.clone(), Box::new(e.clone())))
                .collect();
            let ast_decl = Decl::Inductive {
                name: name.clone(),
                params: params.clone(),
                sort: Box::new(sort.clone()),
                ctors: ast_ctors,
            };
            elab_decl(st, env, &ast_decl).map_err(CheckError::Elab)?;
            let (_ind_term, ind_ty) = st.globals[name].clone();
            Ok(DeclResult { name: name.clone(), kind: DeclKind::Inductive, ty: ind_ty })
        }

        SurfaceDecl::Import { path } => {
            let dir = base_dir.ok_or_else(|| CheckError::ParseError(
                format!("import \"{path}\" requires a file path context (use check_path)")
            ))?;
            let import_path = dir.join(path);
            check_path(&import_path, st, env)
                .map_err(|(_, e)| e)?;
            Ok(DeclResult { name: format!("import \"{path}\""), kind: DeclKind::Def, ty: Term::Sort(0) })
        }

        SurfaceDecl::CheckCmd(expr) => {
            // #check expr — elaborate and print type, don't add to env
            let (_term, ty) = elab_expr(st, env, expr).map_err(CheckError::Elab)?;
            let ty_z = st.mctx.zonk(&ty);
            Ok(DeclResult { name: "#check".into(), kind: DeclKind::Def, ty: ty_z })
        }
    }
}

fn check_theorem(
    st: &mut ElabState,
    env: &Env,
    name: &str,
    params: &[Binder],
    ty_expr: &Expr,
    proof: &Proof,
) -> Result<DeclResult, CheckError> {
    let n_before = st.locals.len();
    let param_types = push_params(st, env, params).map_err(CheckError::Elab)?;
    let n_params = st.locals.len() - n_before;

    let (ty_term, _) = elab_expr(st, env, ty_expr).map_err(CheckError::Elab)?;
    let ty_z = st.mctx.zonk(&ty_term);

    // Elaborate the proof
    match run_proof(st, env, proof, &ty_z) {
        Ok(term) => {
            let proof_z = st.mctx.zonk(&term);
            let ctx = st.ctx();
            kernel::check(env, &ctx, &proof_z, &ty_z)?;
            for _ in 0..n_params { st.pop(); }
            let closed_body = fold_lam(&param_types, proof_z);
            let closed_ty   = fold_pi (&param_types, ty_z.clone());
            st.globals.insert(name.to_string(), (closed_body, closed_ty.clone()));
            return Ok(DeclResult { name: name.to_string(), kind: DeclKind::Theorem, ty: closed_ty });
        }
        Err(RunError::Sorry(msg)) => eprintln!("warning: sorry in '{name}': {msg}"),
        Err(e) => return Err(CheckError::from(e)),
    }

    // Close over params (sorry path: accept as axiom with body = type)
    for _ in 0..n_params { st.pop(); }
    let closed_ty = fold_pi(&param_types, ty_z);
    st.globals.insert(name.to_string(), (closed_ty.clone(), closed_ty.clone()));
    Ok(DeclResult { name: name.to_string(), kind: DeclKind::Theorem, ty: closed_ty })
}

fn elab_def_term(
    st: &mut ElabState,
    env: &Env,
    params: &[Binder],
    ty_expr: &Expr,
    body_expr: &Expr,
) -> Result<(Term, Term), CheckError> {
    let n_before = st.locals.len();
    let param_types = push_params(st, env, params).map_err(CheckError::Elab)?;
    let n_params = st.locals.len() - n_before;

    let (ty_term, _)   = elab_expr(st, env, ty_expr).map_err(CheckError::Elab)?;
    let (body_term, _) = elab_expr(st, env, body_expr).map_err(CheckError::Elab)?;

    let ctx = st.ctx();
    let ty_z   = st.mctx.zonk(&ty_term);
    let body_z = st.mctx.zonk(&body_term);

    kernel::check(env, &ctx, &body_z, &ty_z)?;

    for _ in 0..n_params { st.pop(); }
    let closed_body = fold_lam(&param_types, body_z);
    let closed_ty   = fold_pi (&param_types, ty_z);

    Ok((closed_ty, closed_body))
}

#[cfg(test)]
mod tests {
    use crate::{
        elab::core::ElabState,
        stdlib::std_env,
        surface::{lex, parse_file, check_file},
    };

    fn run(src: &str) -> Result<Vec<super::DeclResult>, String> {
        let mut env = std_env();
        let mut st  = ElabState::new();
        st.add_stdlib();
        let toks = lex(src).map_err(|e| format!("lex: {e:?}"))?;
        let decls = parse_file(&toks).map_err(|e| format!("parse: {e:?}"))?;
        check_file(&decls, &mut st, &mut env).map_err(|(n, e)| format!("{n}: {e}"))
    }

    #[test]
    fn add_zero_induction() {
        let src = r#"
            theorem add_zero (n : Nat) : Eq Nat (Nat.add n 0) n := by {
              induction n
              · rfl
              · intro n ih
                simp
                rewrite [ih]
                rfl
            }
        "#;
        run(src).expect("add_zero should check");
    }

    #[test]
    fn eq_symm_rewrite_backwards() {
        let src = r#"
            theorem eq_symm (n m : Nat) (h : Eq Nat n m) : Eq Nat m n := by {
              rewrite [← h]
              rfl
            }
        "#;
        run(src).expect("eq_symm via rewrite [← h] should check");
    }

    #[test]
    fn proof_file_t2() {
        let src = include_str!("../../../../nox/proofs/T2.ei");
        run(src).expect("T2.ei should check");
    }

    #[test]
    fn proof_file_gravity() {
        let src = include_str!("../../../../prysm/proofs/Gravity.ei");
        run(src).expect("Gravity.ei should check");
    }

    #[test]
    fn proof_file_protocol() {
        let src = include_str!("../../../../prysm/proofs/Protocol.ei");
        run(src).expect("Protocol.ei should check");
    }

    #[test]
    fn proof_file_sizing() {
        let path = std::path::Path::new(concat!(
            env!("CARGO_MANIFEST_DIR"), "/../../prysm/proofs/Sizing.ei"
        ));
        let mut env = crate::stdlib::std_env();
        let mut st  = ElabState::new();
        st.add_stdlib();
        super::check_path(path, &mut st, &mut env)
            .map_err(|(n, e)| format!("{n}: {e}"))
            .expect("Sizing.ei should check");
    }

    #[test]
    fn proof_file_container() {
        let src = include_str!("../../../../prysm/proofs/Container.ei");
        run(src).expect("Container.ei should check");
    }

    #[test]
    fn proof_file_algebra() {
        let src = include_str!("../../../../prysm/proofs/Algebra.ei");
        run(src).expect("Algebra.ei should check");
    }

    #[test]
    fn proof_file_fold() {
        let src = include_str!("../../../../prysm/proofs/Fold.ei");
        run(src).expect("Fold.ei should check");
    }

    #[test]
    fn proof_file_model() {
        let src = include_str!("../../../../nox/proofs/Model.ei");
        run(src).expect("Model.ei should check");
    }

    #[test]
    fn proof_file_t3() {
        let path = std::path::Path::new(concat!(
            env!("CARGO_MANIFEST_DIR"), "/../../nox/proofs/T3.ei"
        ));
        let mut env = crate::stdlib::std_env();
        let mut st  = ElabState::new();
        st.add_stdlib();
        super::check_path(path, &mut st, &mut env)
            .map_err(|(n, e)| format!("{n}: {e}"))
            .expect("T3.ei should check");
    }

    #[test]
    fn proof_file_t1() {
        let path = std::path::Path::new(concat!(
            env!("CARGO_MANIFEST_DIR"), "/../../nox/proofs/T1.ei"
        ));
        let mut env = crate::stdlib::std_env();
        let mut st  = ElabState::new();
        st.add_stdlib();
        super::check_path(path, &mut st, &mut env)
            .map_err(|(n, e)| format!("{n}: {e}"))
            .expect("T1.ei should check");
    }

    #[test]
    fn proof_file_multimodal() {
        let path = std::path::Path::new(concat!(
            env!("CARGO_MANIFEST_DIR"), "/../../prysm/proofs/Multimodal.ei"
        ));
        let mut env = crate::stdlib::std_env();
        let mut st  = ElabState::new();
        st.add_stdlib();
        super::check_path(path, &mut st, &mut env)
            .map_err(|(n, e)| format!("{n}: {e}"))
            .expect("Multimodal.ei should check");
    }
}

fn decl_name(d: &SurfaceDecl) -> Option<&str> {
    match d {
        SurfaceDecl::Def      { name, .. } => Some(name),
        SurfaceDecl::Theorem  { name, .. } => Some(name),
        SurfaceDecl::Axiom    { name, .. } => Some(name),
        SurfaceDecl::Inductive{ name, .. } => Some(name),
        SurfaceDecl::Import   { path }     => Some(path),
        SurfaceDecl::CheckCmd(_)           => None,
    }
}
