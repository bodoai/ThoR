/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Shared.Syntax.Relation.Expr.expr

namespace Shared

  /--
  This inductive type represents an cardinal expression.
  -/
  inductive cardExpr
    | cardExpression : (expression : expr) → cardExpr
  deriving Repr

  /--
  This syntax represents an cardinal expression
  -/
  declare_syntax_cat cardExpr
  syntax "# " expr : cardExpr

  instance : ToString cardExpr where
    toString (ce : cardExpr) : String :=
      match ce with
        | cardExpr.cardExpression e => s!"# {e}"

  namespace cardExpr

    /--
    Generates a string representation of the type
    -/
    def toString (ce : cardExpr) : String := ToString.toString ce

  end cardExpr

end Shared
