//! Routines the parser uses to classify AST nodes

// Predicates on exprs and stmts that the pretty-printer and parser use

use crate::{ast, token::Delimiter};

/// Does this expression require a semicolon to be treated
/// as a statement? The negation of this: 'can this expression
/// be used as a statement without a semicolon' -- is used
/// as an early-bail-out in the parser so that, for instance,
///     if true {...} else {...}
///      |x| 5
/// isn't parsed as (if true {...} else {...} | x) | 5
pub fn expr_requires_semi_to_be_stmt(e: &ast::Expr) -> bool {
    !matches!(
        e.kind,
        ast::ExprKind::If(..)
            | ast::ExprKind::Match(..)
            | ast::ExprKind::Block(..)
            | ast::ExprKind::While(..)
            | ast::ExprKind::Loop(..)
            | ast::ExprKind::ForLoop { .. }
            | ast::ExprKind::TryBlock(..)
            | ast::ExprKind::ConstBlock(..)
    )
}

/// If an expression ends with `}`, returns the innermost expression ending in the `}`
pub fn expr_trailing_brace(mut expr: &ast::Expr) -> Option<&ast::Expr> {
    use ast::ExprKind::*;

    loop {
        match &expr.kind {
            AddrOf(_, _, e)
            | Assign(_, e, _)
            | AssignOp(_, _, e)
            | Binary(_, _, e)
            | Break(_, Some(e))
            | Let(_, e, _, _)
            | Range(_, Some(e), _)
            | Ret(Some(e))
            | Unary(_, e)
            | Yield(Some(e))
            | Yeet(Some(e))
            | Become(e) => {
                expr = e;
            }
            Closure(closure) => {
                expr = &closure.body;
            }
            Gen(..)
            | Block(..)
            | ForLoop { .. }
            | If(..)
            | Loop(..)
            | Match(..)
            | Struct(..)
            | TryBlock(..)
            | While(..)
            | CilkSpawn(..)
            | ConstBlock(_) => break Some(expr),

            MacCall(mac) => {
                break (mac.args.delim == Delimiter::Brace).then_some(expr);
            }

            InlineAsm(_) | OffsetOf(_, _) | IncludedBytes(_) | FormatArgs(_) => {
                // These should have been denied pre-expansion.
                break None;
            }

            Break(_, None)
            | Range(_, None, _)
            | Ret(None)
            | Yield(None)
            | Array(_)
            | Call(_, _)
            | MethodCall(_)
            | Tup(_)
            | Lit(_)
            | Cast(_, _)
            | Type(_, _)
            | Await(_, _)
            | Field(_, _)
            | Index(_, _, _)
            | Underscore
            | Path(_, _)
            | Continue(_)
            | Repeat(_, _)
            | Paren(_)
            | Try(_)
            | Yeet(None)
            | CilkSync
            | Err => break None,
        }
    }
}
