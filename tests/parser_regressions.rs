use gosyn::ast::{Declaration, Expression};
use gosyn::{parse_source, Error};

#[test]
fn parses_complex_type_arguments_across_declarations() {
    let arguments = [
        "int",
        "*int",
        "pkg.T",
        "(int)",
        "Box[int]",
        "map[string]int",
        "[]int",
        "[3]int",
        "chan int",
        "<-chan int",
        "chan<- int",
        "func()",
        "func(int) int",
        "struct{}",
        "interface{}",
        "interface{ M() }",
        "**int",
        "*[]int",
        "(*[]int)",
        "Box[func(int)]",
    ];

    for argument in arguments {
        let declarations = [
            format!("func f(Box[{argument}]) {{}}"),
            format!("func f(x Box[{argument}]) {{}}"),
            format!("func f(Box[{argument},]) {{}}"),
            format!("type S struct {{ Box[{argument}] }}"),
            format!("type S struct {{ *Box[{argument}] }}"),
            format!("type S struct {{ pkg.Box[{argument}] }}"),
            format!("func f() Box[{argument}] {{}}"),
            format!("func f() (Box[{argument}]) {{}}"),
            format!("func f(Pair[{argument}, int]) {{}}"),
            format!("func f(Pair[int, {argument}]) {{}}"),
        ];

        for declaration in declarations {
            let source = format!(
                "package p\ntype Box[T any] struct{{}}\ntype Pair[A, B any] struct{{}}\n{declaration}\n"
            );
            parse_source(&source)
                .unwrap_or_else(|error| panic!("failed to parse {declaration}: {error}"));
        }
    }
}

#[test]
fn preserves_generic_structs_with_pointer_constraints() {
    for constraint in [
        "*[]int",
        "**[]int",
        "(*[]int)",
        "*(*[]int)",
        "*int | *[]int",
    ] {
        let source = format!("package p\ntype X[P {constraint}] struct{{}}\n");
        let file = parse_source(&source).unwrap();
        let Declaration::Type(types) = &file.decl[0] else {
            panic!("expected a type declaration: {source}");
        };
        let spec = &types.specs[0];

        assert_eq!(spec.params.list.len(), 1, "{source}");
        assert_eq!(spec.params.list[0].name.len(), 1, "{source}");
        assert_eq!(spec.params.list[0].name[0].name, "P", "{source}");
        assert!(matches!(spec.typ, Expression::TypeStruct(_)), "{source}");
    }
}

#[test]
fn preserves_array_declarations_that_resemble_type_parameters() {
    for length in ["P * C", "P(C)", "P * C | Q"] {
        let source = format!("package p\ntype X[{length}] int\n");
        let file = parse_source(&source).unwrap();
        let Declaration::Type(types) = &file.decl[0] else {
            panic!("expected a type declaration: {source}");
        };
        let spec = &types.specs[0];

        assert!(spec.params.list.is_empty(), "{source}");
        assert!(matches!(spec.typ, Expression::TypeArray(_)), "{source}");
    }
}

#[test]
fn rejects_invalid_interfaces_without_panicking() {
    for body in [
        "interface int }",
        "interface { $ }",
        "interface { \"unterminated }",
    ] {
        let source = format!("package p\ntype I {body}\n");
        assert!(parse_source(&source).is_err(), "{source}");
    }
}

#[test]
fn qualified_type_position_starts_at_the_package_name() {
    let source = "package p\nvar x pkg.T\n";
    let file = parse_source(source).unwrap();
    let Declaration::Variable(vars) = &file.decl[0] else {
        panic!("expected a variable declaration");
    };

    assert_eq!(
        vars.specs[0].typ.as_ref().unwrap().pos(),
        source.find("pkg.T").unwrap()
    );
}

#[test]
fn preserves_error_locations_after_multiline_type_arguments() {
    let source = "package p\nfunc f(Box[\n int,\n]) {\n @\n}\n";
    let error = parse_source(source).unwrap_err();
    let Error::Else { location, .. } = error.downcast_ref::<Error>().unwrap() else {
        panic!("expected a scanner error: {error}");
    };

    assert_eq!(*location, (4, 1));
}
