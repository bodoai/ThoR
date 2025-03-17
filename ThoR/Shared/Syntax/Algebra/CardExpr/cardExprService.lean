/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Algebra.CardExpr.cardExpr
import ThoR.Shared.Syntax.Relation.Expr.exprService

open Lean

namespace Shared.cardExpr

  /--
  Parses the given syntax to the type
  -/
  def toType (ce : CardExpr) : cardExpr :=
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

end Shared.cardExpr
