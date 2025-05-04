use crate::c4::{Expr, Stmt};

/// A trait for AST visitors, enabling operations like type checking and code generation.
///
/// Implements the Visitor pattern for traversing the AST, allowing different operations
/// without modifying the AST structure itself. This trait enables separation of concerns
/// and flexibility in implementing different compiler phases.
pub trait AstVisitor {
    type Output;
    
    fn visit_expr(&mut self, expr: &Expr) -> Self::Output;
    fn visit_stmt(&mut self, stmt: &Stmt) -> Self::Output;
}

/// A pretty printer for AST nodes, useful for debugging and visualization.
///
/// Converts AST nodes to a formatted string representation, enhancing
/// readability when debugging the parser output.
pub struct PrettyPrinter {
    indent: usize,
}

impl PrettyPrinter {
    pub fn new() -> Self {
        PrettyPrinter { indent: 0 }
    }
    
    fn get_indent(&self) -> String {
        " ".repeat(self.indent * 2)
    }
}

impl AstVisitor for PrettyPrinter {
    type Output = String;
    
    fn visit_expr(&mut self, expr: &Expr) -> Self::Output {
        match expr {
            Expr::Num(n) => format!("{}", n),
            Expr::String(s) => format!("\"{}\"", s),
            Expr::Var(id) => id.clone(),
            Expr::Call(func, args) => {
                let args_str = args.iter()
                    .map(|arg| self.visit_expr(arg))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}({})", func, args_str)
            },
            Expr::UnaryOp(op, expr) => {
                format!("{}({})", op, self.visit_expr(expr))
            },
            Expr::BinOp(left, op, right) => {
                format!("({} {} {})", 
                    self.visit_expr(left), 
                    op, 
                    self.visit_expr(right)
                )
            },
        }
    }
    
    fn visit_stmt(&mut self, stmt: &Stmt) -> Self::Output {
        let indent = self.get_indent();
        
        match stmt {
            Stmt::Expr(expr) => {
                format!("{}{};", indent, self.visit_expr(expr))
            },
            Stmt::Assign(var, expr) => {
                format!("{}{} = {};", indent, var, self.visit_expr(expr))
            },
            Stmt::Return(expr) => {
                format!("{}return {};", indent, self.visit_expr(expr))
            },
            Stmt::If(cond, then_block, else_block) => {
                let mut result = format!("{}if ({}) {{\n", indent, self.visit_expr(cond));
                
                self.indent += 1;
                for stmt in then_block {
                    result.push_str(&format!("{}\n", self.visit_stmt(stmt)));
                }
                self.indent -= 1;
                
                result.push_str(&format!("{}}}", indent));
                
                if let Some(else_stmts) = else_block {
                    result.push_str(&format!(" else {{\n"));
                    
                    self.indent += 1;
                    for stmt in else_stmts {
                        result.push_str(&format!("{}\n", self.visit_stmt(stmt)));
                    }
                    self.indent -= 1;
                    
                    result.push_str(&format!("{}}}", indent));
                }
                
                result
            },
            Stmt::While(cond, block) => {
                let mut result = format!("{}while ({}) {{\n", indent, self.visit_expr(cond));
                
                self.indent += 1;
                for stmt in block {
                    result.push_str(&format!("{}\n", self.visit_stmt(stmt)));
                }
                self.indent -= 1;
                
                result.push_str(&format!("{}}}", indent));
                
                result
            },
            Stmt::For(init, cond, update, block) => {
                let init_str = match init {
                    Some(init) => self.visit_stmt(init),
                    None => String::new(),
                };
                
                let cond_str = match cond {
                    Some(cond) => self.visit_expr(cond),
                    None => String::new(),
                };
                
                let update_str = match update {
                    Some(update) => self.visit_stmt(update),
                    None => String::new(),
                };
                
                let mut result = format!("{}for ({} {}; {}) {{\n", 
                    indent, 
                    init_str.trim_start_matches(&indent).trim_end_matches(';'),
                    cond_str,
                    update_str.trim_start_matches(&indent).trim_end_matches(';')
                );
                
                self.indent += 1;
                for stmt in block {
                    result.push_str(&format!("{}\n", self.visit_stmt(stmt)));
                }
                self.indent -= 1;
                
                result.push_str(&format!("{}}}", indent));
                
                result
            },
        }
    }
}