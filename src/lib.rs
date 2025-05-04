// src/lib.rs
//! C4 Rust - A Rust implementation of the C4 compiler
//!
//! This library provides a Rust reimplementation of the C4 compiler,
//! maintaining compatibility with the original while leveraging Rust's
//! safety features and modern language constructs.

// Export the main modules
pub mod c4;
pub mod utils;
pub mod vm;

// Re-export commonly used items for convenience
pub use c4::{Lexer, Parser, Token, Expr, Stmt, CompilerError, CompilerResult};
pub use vm::VM;
pub use utils::{AstVisitor, PrettyPrinter};
