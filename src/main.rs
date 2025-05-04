mod c4;
mod utils;

use c4::{Lexer, Parser};
use utils::{PrettyPrinter, AstVisitor};
fn main() {
    // Example C code that the parser can handle
    let code = r#"
    {
        x = 10;
        
        if (x > 5) {
            printf("x is greater than 5: %d\n", x);
        } else {
            printf("x is not greater than 5\n");
        }
        
        i = 0;
        while (i < x) {
            printf("Iteration: %d\n", i);
            i = i + 1;
        }
        
        return 0;
    }
    "#;
    
    // Create a parser and parse the code
    let mut parser = Parser::new(code);
    
    // Parse the input as a block of statements
    match parser.parse_block() {
        Ok(stmts) => {
            println!("Successfully parsed the input!");
            
            // Use the pretty printer to display the AST
            let mut printer = PrettyPrinter::new();
            for stmt in &stmts {
                println!("{}", printer.visit_stmt(stmt));
            }
        },
        Err(e) => {
            println!("Failed to parse: {}", e);
        }
    }
}