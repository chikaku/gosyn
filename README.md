# gosyn

Golang's syntax parser in Rust follow by the [Specification](https://go.dev/ref/spec).

Performance is bad for now because of many unnecessary utf-8 decode in scanner(see #1 and [flamegraph](./.github/flamegraph.svg) for details).

## documentation

See https://docs.rs/gosyn
