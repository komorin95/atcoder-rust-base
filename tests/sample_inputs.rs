use cli_test_dir::*;

const BIN: &'static str = "./main";

#[test]
fn sample1() {
    let testdir = TestDir::new(BIN, "");
    let output = testdir
        .cmd()
        .output_with_stdin(r#"
a
"#)
        .tee_output()
        .expect_success();
    assert_eq!(output.stdout_str(), r#"
a
"#);
    assert!(output.stderr_str().is_empty());
}

#[test]
fn sample2() {
    let testdir = TestDir::new(BIN, "");
    let output = testdir
        .cmd()
        .output_with_stdin(r#"
a
"#)
        .tee_output()
        .expect_success();
    assert_eq!(output.stdout_str(), r#"
a
"#);
    assert!(output.stderr_str().is_empty());
}

#[test]
fn sample3() {
    let testdir = TestDir::new(BIN, "");
    let output = testdir
        .cmd()
        .output_with_stdin(r#"
a
"#)
        .tee_output()
        .expect_success();
    assert_eq!(output.stdout_str(), r#"
a
"#);
    assert!(output.stderr_str().is_empty());
}

