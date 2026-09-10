use cyber_eidos::{
    kernel, stdlib,
    surface::{check_strict_path, check_strict_source},
    term::Term,
};

#[test]
fn checks_explicit_law_parameters_and_dependencies() {
    let module = check_strict_source(
        "def id (n : Nat) : Nat := n\ntheorem ok (n : Nat) : Eq Nat (id n) n := by { rfl }",
    )
    .unwrap();
    assert_eq!(module.declarations.len(), 2);
}

#[test]
fn rejects_admissions_holes_wrong_types_and_shadowing() {
    for source in [
        "theorem bad : Eq Nat 0 1 := by { rfl }",
        "theorem bad : Eq Nat 0 1 := by { sorry }",
        "theorem bad : Eq Nat 0 1 := _",
        "axiom bad : Eq Nat 0 1",
        "theorem value : Nat := 0",
        "def Nat : Type := Bool",
        "def x : Nat := 0\ndef x : Nat := 1",
        "def bad : Nat := Nat.div 1 1",
        "inductive X : Type | x : X",
        "#check Nat",
    ] {
        assert!(check_strict_source(source).is_err(), "accepted {source}");
    }
}

#[test]
fn proposition_domain_does_not_lower_data_universe() {
    let env = stdlib::std_env();
    let proposition = Term::Ind(
        stdlib::EQ_ID,
        vec![stdlib::nat(), stdlib::nat_zero(), stdlib::nat_zero()],
    );
    let ty = Term::Pi(Box::new(proposition), Box::new(stdlib::nat()));
    assert_eq!(kernel::infer(&env, &vec![], &ty), Ok(Term::Sort(1)));
    assert_eq!(Term::prop_max(3, 0), 0);
    assert_eq!(Term::prop_max(0, 3), 3);
}

#[test]
fn ordinary_checker_also_rejects_sorry() {
    use cyber_eidos::{
        elab::ElabState,
        surface::{check_file, lex, parse_file},
    };
    let mut state = ElabState::new();
    state.add_stdlib();
    let decls = parse_file(&lex("theorem bad : Eq Nat 0 1 := by { sorry }").unwrap()).unwrap();
    assert!(check_file(&decls, &mut state, &mut stdlib::std_env()).is_err());
    assert!(!state.globals.contains_key("bad"));
}

#[test]
fn imports_are_checked_transitively_cycles_rejected_and_diamonds_shared() {
    let dir = std::env::temp_dir().join(format!("eidos-strict-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let put = |name: &str, src: &str| std::fs::write(dir.join(name), src).unwrap();
    put("common.ei", "def id (n : Nat) : Nat := n");
    put("left.ei", "import \"common.ei\"");
    put("right.ei", "import \"common.ei\"");
    put("root.ei", "import \"left.ei\"\nimport \"right.ei\"\ntheorem ok (n : Nat) : Eq Nat (id n) n := by { rfl }");
    let module = check_strict_path(&dir.join("root.ei")).unwrap();
    assert_eq!(module.files.len(), 4);
    assert_eq!(module.declarations.len(), 2);
    put("common.ei", "axiom hidden : Eq Nat 0 1");
    assert!(check_strict_path(&dir.join("root.ei")).is_err());
    put("common.ei", "import \"root.ei\"");
    assert!(check_strict_path(&dir.join("root.ei"))
        .unwrap_err()
        .contains("cycle"));
    std::fs::remove_dir_all(dir).unwrap();
}
