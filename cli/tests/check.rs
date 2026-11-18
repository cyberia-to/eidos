use std::{fs, process::Command};

/// `eidos check <file.ei>` must resolve `import` relative to the file's directory.
#[test]
fn cli_check_follows_imports() {
    let dir = std::env::temp_dir().join(format!("eidos-cli-check-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("lib.ei"), "def one : Nat := 1\n").unwrap();
    let main = dir.join("main.ei");
    fs::write(&main, "import \"lib.ei\"\ndef two : Nat := Nat.next one\n").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_eidos"))
        .arg("check")
        .arg(&main)
        .output()
        .unwrap();

    assert!(output.status.success(), "{output:?}");
    fs::remove_dir_all(dir).unwrap();
}
