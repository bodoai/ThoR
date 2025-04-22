/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Algebra
import ThoR.Shared.Syntax.Relation.Expr.exprService

open Lean

namespace Shared.algExpr

  private def unhygienicUnfolder
    (input : Unhygienic (Term))
    : Term := Unhygienic.run do
    return ← input

  /--
  Parses the given syntax to the type
  -/
  partial def toType
    (ae : AlgExpr)
    : Except String algExpr := do
      match ae with
        | `(algExpr| $number:num) =>
          return algExpr.number (number.getNat : Int)

        | `(algExpr| # $e:expr) =>
          return (algExpr.cardExpression (← expr.toType e))

        | `(algExpr|
            $op:unAlgOp
            $algExpr1:algExpr) =>
          return algExpr.unaryAlgebraOperation
            (← unAlgOp.toType op) (← toType algExpr1)

        | `(algExpr|
            $op:binAlgOp
            [$algExpr1:algExpr,
            $algExpr2:algExpr]) =>
          return algExpr.binaryAlgebraOperation
            (← binAlgOp.toType op) (← toType algExpr1) (← toType algExpr2)

        | syntx => throw s!"No match implemented in \
            algExprService.toType \
            for '{syntx}'"

  /--
  Gets the required variables for the algebra expression.

  Only needed for cardinal expression here.
  -/
  def getReqVariables
    (ae : algExpr)
    : List (String) := Id.run do
      match ae with
        | algExpr.number _ => []
        | algExpr.cardExpression e => e.getReqVariables
        | algExpr.unaryAlgebraOperation _ ae => ae.getReqVariables
        | algExpr.binaryAlgebraOperation _ ae1 ae2 =>
            ae1.getReqVariables ++  ae2.getReqVariables

end Shared.algExpr
