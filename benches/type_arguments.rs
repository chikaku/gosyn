use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use gosyn::parse_source;

fn nested_function_type_arguments(c: &mut Criterion) {
    let mut group = c.benchmark_group("nested_function_type_arguments");

    for depth in [4, 8, 12, 16, 20] {
        let mut typ = "int".to_string();
        for _ in 0..depth {
            typ = format!("Box[func({typ})]");
        }
        let source = format!("package p\ntype Box[T any] struct{{}}\nfunc f({typ}) {{}}\n");

        group.bench_with_input(BenchmarkId::from_parameter(depth), &source, |b, source| {
            b.iter(|| parse_source(black_box(source)).unwrap());
        });
    }

    group.finish();
}

criterion_group!(benches, nested_function_type_arguments);
criterion_main!(benches);
