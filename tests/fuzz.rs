use gosyn::parse_source;

#[test]
fn parse_fuzz_input() {
    let _ = parse_source(include_str!("testdata/fuzz001.go.txt"));
}
