/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Algebra.CardExpr.cardExpr
import ThoR.Shared.Syntax.Relation.Expr.exprService
import ThoR.Alloy.Exceptions.NoMatchImplementedException

open Lean

namespace Shared.cardExpr

  /--
  Parses the given syntax to the type
  -/
  def toType
    (ce : CardExpr)
    : Except String cardExpr := do
      match ce with
        | `(cardExpr| # $e:expr) =>
          return (cardExpr.cardExpression (← expr.toType e))
        | syntx =>
          throwNoMatchImplemented "cardExprService.toType" syntx

  /--
  Gets the required variables for the cardial expression.
  -/
  def getReqVariables
    (ce : cardExpr)
    : List (String) := Id.run do
      match ce with
        | cardExpr.cardExpression e => e.getReqVariables

end Shared.cardExpr
