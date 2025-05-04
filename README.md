# c4_rust_alwathba
# C4 Rust Implementation

This project is a Rust rewrite of the C4 compiler, maintaining its self-hosting capability and core functionality while leveraging Rust's safety features and modern language constructs.

## Overview

The C4 compiler is a minimalistic self-hosting C compiler originally written in C. This Rust implementation maintains compatibility with the original while taking advantage of Rust's memory safety, pattern matching, and error handling features.

Key components:
- **Lexer**: Tokenizes C source code
- **Parser**: Builds an Abstract Syntax Tree (AST) from tokens
- **Virtual Machine**: Executes the compiled code

## Features

- Self-hosting: Can compile the original C4 source code
- Maintains compatibility with C4's C subset
- Enhanced error reporting with line numbers and contextual messages
- Comprehensive test suite validating each component
- Memory safety guarantees through Rust's ownership model

## Current Limitations

- Loop constructs (for loops and while loops) are not fully functional in the current implementation
- The virtual machine directly interprets the AST rather than generating intermediate code

## Getting Started

### Prerequisites

- Rust toolchain (1.70.0 or newer)
- Cargo package manager

### Building from Source

1. Clone the repository:
   ```bash
   git clone https://github.com/1971cmd/c4_rust_alwathba.git
   cd c4_rust_alwathba
   ```

2. Build the project:
   ```bash
   cargo build --release
   ```

3. Run the compiler:
   ```bash
   cargo run --release -- examples/hello.c
   ```

### Running Tests

Execute the test suite to verify compiler functionality:

```bash
cargo test
```

For more detailed test output:

```bash
cargo test -- --nocapture
```

## Usage Examples

### Compiling C Code

```bash
# Compile a C file
cargo run --release -- examples/hello.c

# Show the AST without executing
cargo run --release -- -ast examples/hello.c
```

## Project Structure

- `src/c4.rs` - Core lexer and parser implementation
- `src/vm.rs` - Virtual machine for executing compiled code
- `src/utils.rs` - Utility functions and AST visitors
- `src/main.rs` - Entry point and CLI handling
- `src/lib.rs` - Library exports for testing and benchmarking
- `examples/` - Example C programs
- `benches/` - Performance benchmarks

## Implementation Details

Our implementation leverages Rust's strong type system and memory safety features:

- Using enums for tokens and AST nodes
- Utilizing Result types for error handling
- Implementing the Visitor pattern for AST traversal
- Employing automatic memory management through Rust's ownership system

## Future Work

- Fully implement loop constructs
- Optimize the execution engine
- Add support for more C language features
- Implement code generation for a real target architecture

## Contributors

- Team Alwathba
