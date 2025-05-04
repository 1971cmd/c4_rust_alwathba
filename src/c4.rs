// src/c4.rs
use std::collections::HashMap;
use std::fmt;
/// Custom error type for lexer and parser operations.
///
/// Provides better error handling with context about where the error occurred
/// and what caused it, leveraging Rust's error handling ecosystem.
#[derive(Debug, Clone)]
pub struct CompilerError {
    message: String,
    line: i32,
}

impl CompilerError {
    pub fn new(message: &str, line: i32) -> Self {
        CompilerError {
            message: message.to_string(),
            line,
        }
    }
}

impl fmt::Display for CompilerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at line {}", self.message, self.line)
    }
}

impl std::error::Error for CompilerError {}

/// Result type for lexer and parser operations.
pub type CompilerResult<T> = Result<T, CompilerError>;

/// Represents the possible tokens produced by the lexer.
///
/// Tokens are the basic building blocks of the source code, such as numbers,
/// identifiers, keywords, operators, strings, preprocessor directives, and an
/// end-of-file marker. This enum ensures type safety and clarity in token handling.
#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    Num(i64),
    Id(String),
    Keyword(String),
    Op(String),
    String(String),
    Directive(String),
    Eof,
}

/// A lexer that tokenizes C source code into a stream of `Token`s.
///
/// The lexer processes the input character by character, recognizing C language
/// constructs like keywords, identifiers, and operators. It maintains state such
/// as the current position and line number for error reporting.
pub struct Lexer {
    input: Vec<char>,
    pos: usize,
    line: i32,
    keywords: HashMap<String, Token>,
}

impl Lexer {
    /// Creates a new `Lexer` instance from a source string.
    ///
    /// Initializes the lexer with the input string and a predefined set of C
    /// keywords. The input is converted to a `Vec<char>` for efficient character
    /// access, and keywords are stored in a `HashMap` for O(1) lookup.
    ///
    /// # Arguments
    /// * `input` - The C source code to tokenize.
    ///
    /// # Returns
    /// A new `Lexer` instance ready to tokenize the input.
    pub fn new(input: &str) -> Self {
        let mut keywords = HashMap::new();
        // Use a more comprehensive list of C keywords
        for kw in [
            "int", "if", "while", "return", "char", "else", "void", "for", 
            "struct", "union", "typedef", "enum", "static", "extern", "const"
        ] {
            keywords.insert(kw.to_string(), Token::Keyword(kw.to_string()));
        }
        Lexer {
            input: input.chars().collect(),
            pos: 0,
            line: 1,
            keywords,
        }
    }

    /// Returns the current line number in the source code.
    ///
    /// Useful for error reporting to indicate where in the source an issue occurred.
    ///
    /// # Returns
    /// The current line number as an `i32`.
    pub fn line(&self) -> i32 {
        self.line
    }
    
    /// Peeks at the current character without advancing the position.
    ///
    /// # Returns
    /// An Option containing the current character, or None if at the end of input.
    fn peek(&self) -> Option<char> {
        if self.pos < self.input.len() {
            Some(self.input[self.pos])
        } else {
            None
        }
    }

    /// Advances the position and returns the current character.
    ///
    /// # Returns
    /// An Option containing the character at the current position before advancing,
    /// or None if at the end of input.
    fn advance(&mut self) -> Option<char> {
        if self.pos < self.input.len() {
            let c = self.input[self.pos];
            self.pos += 1;
            if c == '\n' {
                self.line += 1;
            }
            Some(c)
        } else {
            None
        }
    }

    /// Skips whitespace characters in the input.
    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if !c.is_whitespace() {
                break;
            }
            self.advance();
        }
    }

    /// Skips a single-line comment in the input.
    fn skip_line_comment(&mut self) {
        while let Some(c) = self.peek() {
            if c == '\n' {
                break;
            }
            self.advance();
        }
    }

    /// Retrieves the next token from the input source.
    ///
    /// Skips whitespace and comments, then identifies and returns the next token.
    /// Supports C features like hexadecimal and octal numbers, string literals with
    /// escapes, and multi-character operators (e.g., `==`, `&&`). Errors are returned
    /// as `CompilerResult::Err` with descriptive messages, leveraging Rust's error handling.
    ///
    /// # Returns
    /// * `Ok(Token)` - The next token in the input.
    /// * `Err(CompilerError)` - An error with context if tokenization fails.
    pub fn next(&mut self) -> CompilerResult<Token> {
        self.skip_whitespace();

        match self.peek() {
            None => Ok(Token::Eof),
            
            Some('/') => {
                self.advance();
                if self.peek() == Some('/') {
                    self.advance();
                    self.skip_line_comment();
                    self.next()
                } else {
                    Ok(Token::Op("/".to_string()))
                }
            },
            
            Some('#') => {
                self.advance();
                let mut directive = String::new();
                
                while let Some(c) = self.peek() {
                    if !c.is_alphabetic() {
                        break;
                    }
                    directive.push(c);
                    self.advance();
                }
                
                self.skip_line_comment();
                
                if directive.is_empty() {
                    Err(CompilerError::new("Empty preprocessor directive", self.line - 1))
                } else {
                    Ok(Token::Directive(directive))
                }
            },
            
            Some(c) if c.is_alphabetic() || c == '_' => {
                let mut id = String::new();
                id.push(c);
                self.advance();
                
                while let Some(c) = self.peek() {
                    if !c.is_alphanumeric() && c != '_' {
                        break;
                    }
                    id.push(c);
                    self.advance();
                }
                
                Ok(self.keywords.get(&id).cloned().unwrap_or(Token::Id(id)))
            },
            
            Some(c) if c.is_digit(10) => {
                let mut num_str = String::new();
                num_str.push(c);
                self.advance();
                
                if c == '0' && self.peek().map_or(false, |c| c.to_ascii_lowercase() == 'x') {
                    self.advance(); // Skip 'x'
                    let mut hex_str = String::new();
                    
                    while let Some(c) = self.peek() {
                        if !c.is_digit(16) {
                            break;
                        }
                        hex_str.push(c);
                        self.advance();
                    }
                    
                    if hex_str.is_empty() {
                        Err(CompilerError::new("Expected hexadecimal digits after '0x'", self.line))
                    } else {
                        match i64::from_str_radix(&hex_str, 16) {
                            Ok(num) => Ok(Token::Num(num)),
                            Err(_) => Err(CompilerError::new("Invalid hexadecimal number", self.line))
                        }
                    }
                } else if c == '0' && self.peek().map_or(false, |c| c.is_digit(8)) {
                    let mut octal_str = String::new();
                    
                    while let Some(c) = self.peek() {
                        if !c.is_digit(8) {
                            break;
                        }
                        octal_str.push(c);
                        self.advance();
                    }
                    
                    match i64::from_str_radix(&octal_str, 8) {
                        Ok(num) => Ok(Token::Num(num)),
                        Err(_) => Err(CompilerError::new("Invalid octal number", self.line))
                    }
                } else {
                    while let Some(c) = self.peek() {
                        if !c.is_digit(10) {
                            break;
                        }
                        num_str.push(c);
                        self.advance();
                    }
                    
                    match num_str.parse() {
                        Ok(num) => Ok(Token::Num(num)),
                        Err(_) => Err(CompilerError::new("Invalid decimal number", self.line))
                    }
                }
            },
            
            Some(c) if "+-*/=<>!&|~(){};,".contains(c) => {
                self.advance();
                let mut op = c.to_string();
                
                if let Some(next_c) = self.peek() {
                    if matches!((c, next_c), 
                        ('=', '=') | ('!', '=') | ('<', '=') | ('>', '=') | 
                        ('&', '&') | ('|', '|') | ('+', '+') | ('-', '-')
                    ) {
                        op.push(next_c);
                        self.advance();
                    }
                }
                
                Ok(Token::Op(op))
            },
            
            Some('"') => {
                self.advance();
                let mut s = String::new();
                
                while let Some(c) = self.peek() {
                    if c == '"' {
                        break;
                    } else if c == '\\' {
                        self.advance();
                        
                        match self.peek() {
                            Some('n') => { self.advance(); s.push('\n'); },
                            Some('r') => { self.advance(); s.push('\r'); },
                            Some('t') => { self.advance(); s.push('\t'); },
                            Some('\\') => { self.advance(); s.push('\\'); },
                            Some('"') => { self.advance(); s.push('"'); },
                            Some('0') => { self.advance(); s.push('\0'); },
                            Some(c) => {
                                self.advance();
                                s.push('\\');
                                s.push(c);
                            },
                            None => return Err(CompilerError::new("Incomplete escape sequence", self.line))
                        }
                    } else {
                        s.push(c);
                        self.advance();
                    }
                }
                
                if self.peek() != Some('"') {
                    Err(CompilerError::new("Unclosed string literal", self.line))
                } else {
                    self.advance(); // Skip closing quote
                    Ok(Token::String(s))
                }
            },
            
            Some(c) => {
                Err(CompilerError::new(&format!("Unexpected character '{}'", c), self.line))
            }
        }
    }
}

/// Represents an expression in the C abstract syntax tree (AST).
///
/// Expressions include literals, variables, function calls, and operations.
/// Using `Box` for recursive variants ensures memory safety and prevents stack
/// overflow, aligning with Rust's ownership model.
#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    Num(i64),
    String(String),
    Var(String),
    Call(String, Vec<Expr>),
    UnaryOp(String, Box<Expr>),
    BinOp(Box<Expr>, String, Box<Expr>),
}

/// Represents a statement in the C abstract syntax tree (AST).
///
/// Statements include expressions, assignments, returns, and control flow
/// constructs like `if` and `while`. This structure mirrors the subset of C
/// supported by the original C4 compiler.
#[derive(Debug, PartialEq, Clone)]
pub enum Stmt {
    Expr(Expr),
    Assign(String, Expr),
    Return(Expr),
    If(Expr, Vec<Stmt>, Option<Vec<Stmt>>),
    While(Expr, Vec<Stmt>),
    For(Option<Box<Stmt>>, Option<Expr>, Option<Box<Stmt>>, Vec<Stmt>),
}

/// A parser that constructs an AST from a stream of tokens.
///
/// Uses a recursive descent approach to parse the C subset supported by C4.
/// Maintains compatibility by handling the same syntax and semantics as the
/// original C implementation, with enhancements for error handling and performance.
pub struct Parser {
    lexer: Lexer,
    current_token: CompilerResult<Token>,
}

impl Parser {
    /// Creates a new `Parser` instance from a source string.
    ///
    /// Initializes the parser with a `Lexer` and fetches the first token.
    ///
    /// # Arguments
    /// * `input` - The C source code to parse.
    ///
    /// # Returns
    /// A new `Parser` instance ready to parse the input.
    pub fn new(input: &str) -> Self {
        let mut lexer = Lexer::new(input);
        let current_token = lexer.next();
        Parser {
            lexer,
            current_token,
        }
    }

    /// Advances the parser to the next token.
    ///
    /// Updates `current_token` with the next token from the lexer.
    ///
    /// # Returns
    /// * `Ok(())` - If advancing succeeds.
    /// * `Err(CompilerError)` - If the lexer encounters an error.
    fn advance(&mut self) -> CompilerResult<()> {
        self.current_token = self.lexer.next();
        Ok(())
    }

    /// Consumes a token if it matches the expected type, otherwise returns an error.
    ///
    /// # Arguments
    /// * `expected` - A function that checks if the token is of the expected type.
    /// * `error_msg` - The error message to return if the token doesn't match.
    ///
    /// # Returns
    /// * `Ok(Token)` - The consumed token if it matches.
    /// * `Err(CompilerError)` - An error message if the token doesn't match.
    fn consume<F>(&mut self, expected: F, error_msg: &str) -> CompilerResult<Token>
    where
        F: FnOnce(&Token) -> bool,
    {
        match &self.current_token {
            Ok(token) if expected(token) => {
                let result = self.current_token.clone();
                self.advance()?;
                result
            },
            _ => Err(CompilerError::new(error_msg, self.lexer.line())),
        }
    }

    /// Checks if the current token is an operator with the given symbol.
    ///
    /// # Arguments
    /// * `symbol` - The operator symbol to check for.
    ///
    /// # Returns
    /// `true` if the current token is an operator with the given symbol, `false` otherwise.
    fn is_op(&self, symbol: &str) -> bool {
        match &self.current_token {
            Ok(Token::Op(op)) => op == symbol,
            _ => false,
        }
    }

    /// Checks if the current token is a keyword with the given name.
    ///
    /// # Arguments
    /// * `name` - The keyword to check for.
    ///
    /// # Returns
    /// `true` if the current token is a keyword with the given name, `false` otherwise.
    fn is_keyword(&self, name: &str) -> bool {
        match &self.current_token {
            Ok(Token::Keyword(kw)) => kw == name,
            _ => false,
        }
    }

    /// Parses a block of statements enclosed in braces or a single statement.
    ///
    /// Handles both braced blocks (e.g., `{ stmt; stmt; }`) and unbraced single
    /// statements, ensuring flexibility and compatibility with C4's syntax.
    ///
    /// # Returns
    /// * `Ok(Vec<Stmt>)` - A vector of parsed statements.
    /// * `Err(CompilerError)` - An error message if parsing fails.
    pub fn parse_block(&mut self) -> CompilerResult<Vec<Stmt>> {
        let mut stmts = Vec::new();
        let mut expect_closing_brace = false;
    
        if self.is_op("{") {
            expect_closing_brace = true;
            self.advance()?;
        }
    
        while !matches!(self.current_token, Ok(Token::Eof)) && !(expect_closing_brace && self.is_op("}")) {
            stmts.push(self.parse_stmt()?);
        }
    
        if expect_closing_brace {
            if !self.is_op("}") {
                return Err(CompilerError::new("Expected '}' at end of block", self.lexer.line()));
            }
            self.advance()?;
        }
    
        Ok(stmts)
    }

    /// Parses a single statement.
    ///
    /// Recognizes statements like `if`, `while`, `for`, `return`, assignments, and
    /// expressions, with enhanced error handling and support for additional C constructs.
    ///
    /// # Returns
    /// * `Ok(Stmt)` - The parsed statement.
    /// * `Err(CompilerError)` - An error message if the statement is malformed.
    pub fn parse_stmt(&mut self) -> CompilerResult<Stmt> {
        match &self.current_token {
            Ok(Token::Keyword(kw)) if kw == "if" => {
                self.advance()?;
                self.consume(|t| matches!(t, Token::Op(op) if op == "("), "Expected '(' after 'if'")?;
                let cond = self.parse_expr()?;
                self.consume(|t| matches!(t, Token::Op(op) if op == ")"), "Expected ')' after if condition")?;
                let then_block = self.parse_block()?;
                
                let else_block = if self.is_keyword("else") {
                    self.advance()?;
                    Some(self.parse_block()?)
                } else {
                    None
                };
                
                Ok(Stmt::If(cond, then_block, else_block))
            },
            
            Ok(Token::Keyword(kw)) if kw == "while" => {
                self.advance()?;
                self.consume(|t| matches!(t, Token::Op(op) if op == "("), "Expected '(' after 'while'")?;
                let cond = self.parse_expr()?;
                self.consume(|t| matches!(t, Token::Op(op) if op == ")"), "Expected ')' after while condition")?;
                let block = self.parse_block()?;
                
                Ok(Stmt::While(cond, block))
            },
            
            Ok(Token::Keyword(kw)) if kw == "for" => {
                self.advance()?;
                self.consume(|t| matches!(t, Token::Op(op) if op == "("), "Expected '(' after 'for'")?;
                
                // Parse initializer
                let init = if self.is_op(";") {
                    self.advance()?;
                    None
                } else {
                    let stmt = self.parse_stmt()?;
                    Some(Box::new(stmt))
                };
                
                // Parse condition
                let cond = if self.is_op(";") {
                    self.advance()?;
                    None
                } else {
                    let expr = self.parse_expr()?;
                    self.consume(|t| matches!(t, Token::Op(op) if op == ";"), "Expected ';' after for condition")?;
                    Some(expr)
                };
                
                // Parse increment
                let incr = if self.is_op(")") {
                    None
                } else {
                    let expr = self.parse_expr()?;
                    let stmt = Stmt::Expr(expr);
                    Some(Box::new(stmt))
                };
                
                self.consume(|t| matches!(t, Token::Op(op) if op == ")"), "Expected ')' after for clauses")?;
                let block = self.parse_block()?;
                
                Ok(Stmt::For(init, cond, incr, block))
            },
            
            Ok(Token::Keyword(kw)) if kw == "return" => {
                self.advance()?;
                let expr = self.parse_expr()?;
                self.consume(|t| matches!(t, Token::Op(op) if op == ";"), "Expected ';' after return")?;
                
                Ok(Stmt::Return(expr))
            },
            
            _ => {
                let expr = self.parse_expr()?;
                
                if self.is_op(";") {
                    self.advance()?;
                    Ok(Stmt::Expr(expr))
                } else if self.is_op("=") {
                    self.advance()?;
                    let rhs = self.parse_expr()?;
                    self.consume(|t| matches!(t, Token::Op(op) if op == ";"), "Expected ';' after assignment")?;
                    
                    match expr {
                        Expr::Var(id) => Ok(Stmt::Assign(id, rhs)),
                        _ => Err(CompilerError::new("Expected variable for assignment", self.lexer.line())),
                    }
                } else {
                    Err(CompilerError::new("Expected '=' or ';' after expression", self.lexer.line()))
                }
            }
        }
    }

    /// Parses an expression, handling logical OR operations.
    ///
    /// Implements operator precedence parsing for expressions, starting with the
    /// lowest precedence (logical OR) and recursively handling higher precedence operations.
    ///
    /// # Returns
    /// * `Ok(Expr)` - The parsed expression.
    /// * `Err(CompilerError)` - An error message if the expression is invalid.
    pub fn parse_expr(&mut self) -> CompilerResult<Expr> {
        self.parse_logical_or()
    }

    /// Parses a logical OR expression (e.g., `a || b`).
    fn parse_logical_or(&mut self) -> CompilerResult<Expr> {
        let mut expr = self.parse_logical_and()?;
        
        while self.is_op("||") {
            self.advance()?;
            let right = self.parse_logical_and()?;
            expr = Expr::BinOp(Box::new(expr), "||".to_string(), Box::new(right));
        }
        
        Ok(expr)
    }

    /// Parses a logical AND expression (e.g., `a && b`).
    fn parse_logical_and(&mut self) -> CompilerResult<Expr> {
        let mut expr = self.parse_equality()?;
        
        while self.is_op("&&") {
            self.advance()?;
            let right = self.parse_equality()?;
            expr = Expr::BinOp(Box::new(expr), "&&".to_string(), Box::new(right));
        }
        
        Ok(expr)
    }

    /// Parses an equality expression (e.g., `a == b` or `a != b`).
    fn parse_equality(&mut self) -> CompilerResult<Expr> {
        let mut expr = self.parse_relational()?;
        
        while self.is_op("==") || self.is_op("!=") {
            let op = match &self.current_token {
                Ok(Token::Op(op)) => op.clone(),
                _ => unreachable!(),
            };
            self.advance()?;
            let right = self.parse_relational()?;
            expr = Expr::BinOp(Box::new(expr), op, Box::new(right));
        }
        
        Ok(expr)
    }

    /// Parses a relational expression (e.g., `a < b`, `a > b`, `a <= b`, `a >= b`).
    fn parse_relational(&mut self) -> CompilerResult<Expr> {
        let mut expr = self.parse_additive()?;
        
        while self.is_op("<") || self.is_op(">") || self.is_op("<=") || self.is_op(">=") {
            let op = match &self.current_token {
                Ok(Token::Op(op)) => op.clone(),
                _ => unreachable!(),
            };
            self.advance()?;
            let right = self.parse_additive()?;
            expr = Expr::BinOp(Box::new(expr), op, Box::new(right));
        }
        
        Ok(expr)
    }

    /// Parses an additive expression (e.g., `a + b` or `a - b`).
    fn parse_additive(&mut self) -> CompilerResult<Expr> {
        let mut expr = self.parse_multiplicative()?;
        
        while self.is_op("+") || self.is_op("-") {
            let op = match &self.current_token {
                Ok(Token::Op(op)) => op.clone(),
                _ => unreachable!(),
            };
            self.advance()?;
            let right = self.parse_multiplicative()?;
            expr = Expr::BinOp(Box::new(expr), op, Box::new(right));
        }
        
        Ok(expr)
    }

    /// Parses a multiplicative expression (e.g., `a * b` or `a / b`).
    fn parse_multiplicative(&mut self) -> CompilerResult<Expr> {
        let mut expr = self.parse_unary()?;
        
        while self.is_op("*") || self.is_op("/") {
            let op = match &self.current_token {
                Ok(Token::Op(op)) => op.clone(),
                _ => unreachable!(),
            };
            self.advance()?;
            let right = self.parse_unary()?;
            expr = Expr::BinOp(Box::new(expr), op, Box::new(right));
        }
        
        Ok(expr)
    }

    /// Parses a unary expression (e.g., `!a` or `-b`).
    fn parse_unary(&mut self) -> CompilerResult<Expr> {
        if self.is_op("!") || self.is_op("-") || self.is_op("~") {
            let op = match &self.current_token {
                Ok(Token::Op(op)) => op.clone(),
                _ => unreachable!(),
            };
            self.advance()?;
            let expr = self.parse_unary()?;
            Ok(Expr::UnaryOp(op, Box::new(expr)))
        } else {
            self.parse_primary()
        }
    }

    /// Parses a primary expression (e.g., literals, variables, function calls).
    fn parse_primary(&mut self) -> CompilerResult<Expr> {
        match &self.current_token {
            Ok(Token::Num(n)) => {
                let n = *n;
                self.advance()?;
                Ok(Expr::Num(n))
            },
            
            Ok(Token::String(s)) => {
                let s = s.clone();
                self.advance()?;
                Ok(Expr::String(s))
            },
            
            Ok(Token::Id(id)) => {
                let id = id.clone();
                self.advance()?;
                
                if self.is_op("(") {
                    self.advance()?;
                    let args = self.parse_args()?;
                    self.consume(|t| matches!(t, Token::Op(op) if op == ")"), "Expected ')' after function arguments")?;
                    Ok(Expr::Call(id, args))
                } else {
                    Ok(Expr::Var(id))
                }
            },
            
            Ok(Token::Op(op)) if op == "(" => {
                self.advance()?;
                let expr = self.parse_expr()?;
                self.consume(|t| matches!(t, Token::Op(op) if op == ")"), "Expected ')' after expression")?;
                Ok(expr)
            },
            
            _ => Err(CompilerError::new(
                "Expected number, string, identifier, unary operator, or '('", 
                self.lexer.line()
            )),
        }
    }

    /// Parses a comma-separated list of arguments for a function call.
    ///
    /// Handles zero or more expressions separated by commas, used in function calls.
    ///
    /// # Returns
    /// * `Ok(Vec<Expr>)` - The list of parsed arguments.
    /// * `Err(CompilerError)` - An error message if the arguments are invalid.
    fn parse_args(&mut self) -> CompilerResult<Vec<Expr>> {
        let mut args = Vec::new();
        
        if !self.is_op(")") {
            args.push(self.parse_expr()?);
            
            while self.is_op(",") {
                self.advance()?;
                args.push(self.parse_expr()?);
            }
        }
        
        Ok(args)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Lexer tests
    #[test]
    fn test_keywords() {
        let mut lexer = Lexer::new("int if while return char");
        assert_eq!(lexer.next(), Ok(Token::Keyword("int".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("if".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("while".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("return".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("char".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Eof));
    }
    
    #[test]
    fn test_extended_keywords() {
        let mut lexer = Lexer::new("void struct union typedef enum static extern const");
        assert_eq!(lexer.next(), Ok(Token::Keyword("void".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("struct".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("union".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("typedef".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("enum".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("static".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("extern".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("const".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Eof));
    }

    #[test]
    fn test_identifier() {
        let mut lexer = Lexer::new("main x123 printf _identifier");
        assert_eq!(lexer.next(), Ok(Token::Id("main".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Id("x123".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Id("printf".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Id("_identifier".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Eof));
    }

    #[test]
    fn test_number() {
        let mut lexer = Lexer::new("123 456 0 42");
        assert_eq!(lexer.next(), Ok(Token::Num(123)));
        assert_eq!(lexer.next(), Ok(Token::Num(456)));
        assert_eq!(lexer.next(), Ok(Token::Num(0)));
        assert_eq!(lexer.next(), Ok(Token::Num(42)));
        assert_eq!(lexer.next(), Ok(Token::Eof));
    }

    #[test]
    fn test_operators() {
        let mut lexer = Lexer::new("+ - * / = == != < > <= >= && || ! ~ ++ --");
        assert_eq!(lexer.next(), Ok(Token::Op("+".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("-".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("*".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("/".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("=".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("==".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("!=".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("<".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op(">".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("<=".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op(">=".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("&&".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("||".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("!".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("~".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("++".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("--".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Eof));
    }

    #[test]
    fn test_string() {
        let mut lexer = Lexer::new("\"hello\" \"world\"");
        assert_eq!(lexer.next(), Ok(Token::String("hello".to_string())));
        assert_eq!(lexer.next(), Ok(Token::String("world".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Eof));
    }

    #[test]
    fn test_string_escape() {
        let mut lexer = Lexer::new("\"hello\\nworld\\\"\\\\\" \"tab\\t\"");
        assert_eq!(lexer.next(), Ok(Token::String("hello\nworld\"\\".to_string())));
        assert_eq!(lexer.next(), Ok(Token::String("tab\t".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Eof));
    }

    #[test]
    fn test_punctuation() {
        let mut lexer = Lexer::new("(){};,");
        assert_eq!(lexer.next(), Ok(Token::Op("(".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op(")".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("{".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op("}".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op(";".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Op(",".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Eof));
    }

    #[test]
    fn test_invalid_character() {
        let mut lexer = Lexer::new("@");
        assert!(matches!(lexer.next(), Err(CompilerError { .. })));
    }

    #[test]
    fn test_directive() {
        let mut lexer = Lexer::new("#include <stdio.h>\n#define MAX 100\nint x");
        assert_eq!(lexer.next(), Ok(Token::Directive("include".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Directive("define".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Keyword("int".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Id("x".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Eof));
        assert_eq!(lexer.line(), 3);
    }

    #[test]
    fn test_comment() {
        let mut lexer = Lexer::new("// comment\nint x");
        assert_eq!(lexer.next(), Ok(Token::Keyword("int".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Id("x".to_string())));
        assert_eq!(lexer.next(), Ok(Token::Eof));
        assert_eq!(lexer.line(), 2);
    }

    #[test]
    fn test_hex_number() {
        let mut lexer = Lexer::new("0xFF 0x123");
        assert_eq!(lexer.next(), Ok(Token::Num(255)));
        assert_eq!(lexer.next(), Ok(Token::Num(291)));
        assert_eq!(lexer.next(), Ok(Token::Eof));
    }

    #[test]
    fn test_octal_number() {
        let mut lexer = Lexer::new("077 0123");
        assert_eq!(lexer.next(), Ok(Token::Num(63)));
        assert_eq!(lexer.next(), Ok(Token::Num(83)));
        assert_eq!(lexer.next(), Ok(Token::Eof));
    }

    #[test]
    fn test_invalid_string() {
        let mut lexer = Lexer::new("\"unclosed");
        assert!(matches!(lexer.next(), Err(CompilerError { .. })));
    }

    #[test]
    fn test_c4_snippet() {
        let input = r#"
        #include <stdio.h>
        int main() {
            char *p = "hello\n";
            if (p != 0) {
                printf("%s", p);
                return 0xFF;
            }
            return 0;
        }
        "#;
        let mut lexer = Lexer::new(input);
        let mut tokens = Vec::new();
        
        loop {
            match lexer.next() {
                Ok(token) => {
                    let is_eof = token == Token::Eof;
                    tokens.push(token);
                    if is_eof {
                        break;
                    }
                },
                Err(e) => {
                    panic!("Unexpected error: {}", e);
                }
            }
        }
        
        assert_eq!(tokens.len(), 35); // 34 tokens + EOF
        assert!(matches!(tokens[0], Token::Directive(_)));
        assert!(matches!(tokens[1], Token::Keyword(_)));
        assert!(matches!(tokens[2], Token::Id(_)));
    }

    // Parser Tests
    #[test]
    fn test_parse_number() {
        let mut parser = Parser::new("42");
        let expr = parser.parse_expr().unwrap();
        assert_eq!(expr, Expr::Num(42));
    }

    #[test]
    fn test_parse_string() {
        let mut parser = Parser::new("\"hello\"");
        let expr = parser.parse_expr().unwrap();
        assert_eq!(expr, Expr::String("hello".to_string()));
    }

    #[test]
    fn test_parse_variable() {
        let mut parser = Parser::new("x");
        let expr = parser.parse_expr().unwrap();
        assert_eq!(expr, Expr::Var("x".to_string()));
    }

    #[test]
    fn test_parse_function_call() {
        let mut parser = Parser::new("printf(\"%s\", p)");
        let expr = parser.parse_expr().unwrap();
        assert_eq!(
            expr,
            Expr::Call(
                "printf".to_string(),
                vec![
                    Expr::String("%s".to_string()),
                    Expr::Var("p".to_string())
                ]
            )
        );
    }

    #[test]
    fn test_parse_unary_minus() {
        let mut parser = Parser::new("-x");
        let expr = parser.parse_expr().unwrap();
        assert_eq!(
            expr, 
            Expr::UnaryOp("-".to_string(), Box::new(Expr::Var("x".to_string())))
        );
    }

    #[test]
    fn test_parse_unary_not() {
        let mut parser = Parser::new("!x");
        let expr = parser.parse_expr().unwrap();
        assert_eq!(
            expr, 
            Expr::UnaryOp("!".to_string(), Box::new(Expr::Var("x".to_string())))
        );
    }

    #[test]
    fn test_parse_complex() {
        let mut parser = Parser::new("x + printf(\"%s\", p) * 2");
        let expr = parser.parse_expr().unwrap();
        assert_eq!(
            expr,
            Expr::BinOp(
                Box::new(Expr::Var("x".to_string())),
                "+".to_string(),
                Box::new(Expr::BinOp(
                    Box::new(Expr::Call(
                        "printf".to_string(),
                        vec![
                            Expr::String("%s".to_string()),
                            Expr::Var("p".to_string())
                        ]
                    )),
                    "*".to_string(),
                    Box::new(Expr::Num(2))
                ))
            )
        );
    }

    #[test]
    fn test_parse_precedence() {
        let mut parser = Parser::new("x + y * 3");
        let expr = parser.parse_expr().unwrap();
        assert_eq!(
            expr,
            Expr::BinOp(
                Box::new(Expr::Var("x".to_string())),
                "+".to_string(),
                Box::new(Expr::BinOp(
                    Box::new(Expr::Var("y".to_string())),
                    "*".to_string(),
                    Box::new(Expr::Num(3))
                ))
            )
        );
    }

    #[test]
    fn test_parse_parentheses() {
        let mut parser = Parser::new("(x + y) * 3");
        let expr = parser.parse_expr().unwrap();
        assert_eq!(
            expr,
            Expr::BinOp(
                Box::new(Expr::BinOp(
                    Box::new(Expr::Var("x".to_string())),
                    "+".to_string(),
                    Box::new(Expr::Var("y".to_string()))
                )),
                "*".to_string(),
                Box::new(Expr::Num(3))
            )
        );
    }

    #[test]
    fn test_parse_expr_stmt() {
        let mut parser = Parser::new("printf(\"%s\", p);");
        let stmt = parser.parse_stmt().unwrap();
        assert_eq!(
            stmt,
            Stmt::Expr(Expr::Call(
                "printf".to_string(),
                vec![
                    Expr::String("%s".to_string()),
                    Expr::Var("p".to_string())
                ]
            ))
        );
    }

    #[test]
    fn test_parse_assign_stmt() {
        let mut parser = Parser::new("x = 5;");
        let stmt = parser.parse_stmt().unwrap();
        assert_eq!(
            stmt,
            Stmt::Assign("x".to_string(), Expr::Num(5))
        );
    }

    #[test]
    fn test_parse_return_stmt() {
        let mut parser = Parser::new("return 0;");
        let stmt = parser.parse_stmt().unwrap();
        assert_eq!(
            stmt,
            Stmt::Return(Expr::Num(0))
        );
    }

    #[test]
    fn test_parse_if_stmt() {
        let mut parser = Parser::new("if (x) { return 5; }");
        let stmt = parser.parse_stmt().unwrap();
        assert_eq!(
            stmt,
            Stmt::If(
                Expr::Var("x".to_string()),
                vec![Stmt::Return(Expr::Num(5))],
                None
            )
        );
    }

    #[test]
    fn test_parse_if_else_stmt() {
        let mut parser = Parser::new("if (x) { return 5; } else { return 0; }");
        let stmt = parser.parse_stmt().unwrap();
        assert_eq!(
            stmt,
            Stmt::If(
                Expr::Var("x".to_string()),
                vec![Stmt::Return(Expr::Num(5))],
                Some(vec![Stmt::Return(Expr::Num(0))])
            )
        );
    }
}
