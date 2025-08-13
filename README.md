# MiniSMT

MiniSMT is a minimal SMT-LIB 2.0 bitvector solver written in Rust. It supports a subset of the SMT-LIB language, focusing on bitvector and boolean logic.

## Features

- Bit-blasting for bitvector operations
- Basic support for SMT-LIB 2.0 commands
- Simple CNF-based SAT solving

## Usage

Build with Cargo

### Logging / Tracing

This project uses the `tracing` ecosystem for structured logging.

- Control verbosity via the standard `RUST_LOG` environment variable.
- Examples:

```bash
# Show high-level info
RUST_LOG=info cargo run -- path/to/file.smt2

# Enable detailed tracing for parser and solver internals
RUST_LOG=trace cargo run -- path/to/file.smt2

# Focus on specific modules
RUST_LOG=minismt=info,minismt::solver=debug,minismt::solver::smtlib=trace cargo run -- path/to/file.smt2
```

Logs are written to stderr by default with timestamps and targets; they won't pollute normal solver stdout results.
