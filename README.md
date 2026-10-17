# gosyn

Golang's syntax parser in Rust follow by the [Specification](https://go.dev/ref/spec).

## documentation

See https://docs.rs/gosyn

## tests

Run the tests, including parser regression cases:

```sh
cargo test --all-features
```

Compare nested generic function type parsing across input depths:

```sh
cargo bench --bench type_arguments
```
