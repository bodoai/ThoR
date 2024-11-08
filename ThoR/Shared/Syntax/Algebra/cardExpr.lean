/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.Relation.expr

open Lean

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

    /--
    Parses the given syntax to the type
    -/
    def toType (ce : TSyntax `cardExpr) : cardExpr :=
      match ce with
        | `(cardExpr| # $e:expr) => (cardExpr.cardExpression (expr.toType e))
        | _ => (cardExpr.cardExpression (expr.const (constant.none))) -- unreachable

    /--
    Gets the required variables for the cardial expression.
    -/
    def getReqVariables
      (ce : cardExpr)
      : List (String) := Id.run do
        match ce with
          | cardExpr.cardExpression e => e.getReqVariables

  end cardExpr

end Shared
