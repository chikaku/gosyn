use gosyn::ast::{Declaration, NameType, Type, TypeTerm};
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

        assert_eq!(spec.params.len(), 1, "{source}");
        assert_eq!(spec.params[0].name.len(), 1, "{source}");
        assert_eq!(spec.params[0].name[0].name, "P", "{source}");
        assert!(matches!(spec.typ, Type::Struct(_)), "{source}");
    }
}

#[test]
fn preserves_pointer_constraint_ast() {
    let file = parse_source("package p\ntype X[P **[]int] struct{}\n").unwrap();
    let Declaration::Type(types) = &file.decl[0] else {
        panic!("expected a type declaration");
    };
    let [TypeTerm::Type(Type::Pointer(outer))] =
        types.specs[0].params[0].constraint.types.as_slice()
    else {
        panic!("expected an outer pointer constraint");
    };
    let Type::Pointer(inner) = outer.typ.as_ref() else {
        panic!("expected an inner pointer constraint");
    };
    let Type::Slice(slice) = inner.typ.as_ref() else {
        panic!("expected a pointer to a slice");
    };
    let Type::Name(NameType::Ident(element)) = slice.typ.as_ref() else {
        panic!("expected a named slice element type");
    };

    assert_eq!(element.name, "int");
}

#[test]
fn preserves_nested_function_type_argument_ast() {
    let source = "package p\ntype Box[T any] struct{}\nfunc f(Box[func(Box[func(int)])]) {}\n";
    let file = parse_source(source).unwrap();
    let Declaration::Function(function) = &file.decl[1] else {
        panic!("expected a function declaration");
    };
    assert_eq!(function.typ.params.parameters.len(), 1);
    assert!(function.typ.params.parameters[0].identifiers.is_empty());

    let mut typ = &function.typ.params.parameters[0].typ;
    for _ in 0..2 {
        let Type::Instantiated(instantiation) = typ else {
            panic!("expected an instantiated type, got {typ:?}");
        };
        let NameType::Ident(name) = &instantiation.name else {
            panic!("expected a named generic type");
        };
        assert_eq!(name.name, "Box");

        let [Type::Function(function)] = instantiation.arguments.as_slice() else {
            panic!("expected a function type argument");
        };
        assert_eq!(function.params.parameters.len(), 1);
        assert!(function.params.parameters[0].identifiers.is_empty());
        assert!(function.result.parameters.is_empty());
        typ = &function.params.parameters[0].typ;
    }

    let Type::Name(NameType::Ident(parameter)) = typ else {
        panic!("expected a named function parameter type");
    };
    assert_eq!(parameter.name, "int");
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

        assert!(spec.params.is_empty(), "{source}");
        assert!(matches!(spec.typ, Type::Array(_)), "{source}");
    }
}

#[test]
fn trailing_comma_disambiguates_type_parameters_from_array_lengths() {
    let source = "package p\ntype X[P * C | Q] int\ntype Z[P *C | Q,] int\n";
    let file = parse_source(source).unwrap();
    let [Declaration::Type(array), Declaration::Type(generic)] = file.decl.as_slice() else {
        panic!("expected two type declarations");
    };
    let array = &array.specs[0];
    assert!(array.params.is_empty());
    assert!(matches!(array.typ, Type::Array(_)));

    let generic = &generic.specs[0];
    assert_eq!(generic.params.len(), 1);
    assert_eq!(generic.params[0].name.len(), 1);
    assert_eq!(generic.params[0].name[0].name, "P");
    let Type::Name(NameType::Ident(typ)) = &generic.typ else {
        panic!("expected a named underlying type");
    };
    assert_eq!(typ.name, "int");
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
