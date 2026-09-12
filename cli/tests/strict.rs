use std::{fs, process::Command};

#[test]
fn cli_strict_success_and_failure_exit_codes() {
    let dir = std::env::temp_dir().join(format!("eidos-cli-strict-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let path = dir.join("proof.ei");
    for (source, success) in [
        ("theorem good : Eq Nat 1 1 := by { rfl }", true),
        ("theorem bad : Eq Nat 0 1 := by { sorry }", false),
        ("axiom hidden : Eq Nat 0 1", false),
    ] {
        fs::write(&path, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_eidos"))
            .arg("check")
            .arg("--strict")
            .arg(&path)
            .output()
            .unwrap();
        assert_eq!(output.status.success(), success, "{output:?}");
        if !success {
            assert!(!String::from_utf8_lossy(&output.stdout).contains("proved"));
        }
    }
    fs::remove_dir_all(dir).unwrap();
}
