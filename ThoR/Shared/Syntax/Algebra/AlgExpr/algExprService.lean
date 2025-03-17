/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Algebra
import ThoR.Shared.Syntax.Algebra.CardExpr.cardExprService

open Lean

namespace Shared.algExpr

  /--
  Generates a Lean term corosponding with the type
  -/
  def toTerm
  (ae : algExpr)
  (blockName : Name)
  : Term := Unhygienic.run do
    match ae with
      | algExpr.number n => `($(Lean.Syntax.mkNumLit s!"{n.natAbs}"):num)
      | algExpr.cardExpr ce =>
        match ce with
          | cardExpr.cardExpression expr =>
            `(($(mkIdent ``ThoR.Card.card) $(expr.toTermFromBlock blockName)))
      | algExpr.unaryAlgebraOperation op ae => `(($(op.toTerm) $(ae.toTerm blockName)))
      | algExpr.binaryAlgebraOperation op ae1 ae2 =>
        `(($(op.toTerm) $(ae1.toTerm blockName) $(ae2.toTerm blockName)))

  /--
  Parses the given syntax to the type
  -/
  partial def toType (ae : AlgExpr) : algExpr :=
    match ae with
      | `(algExpr| $number:num) =>
        algExpr.number (number.getNat : Int)

      | `(algExpr| $ce:cardExpr) =>
        algExpr.cardExpr (cardExpr.toType ce)

      | `(algExpr|
          $op:unAlgOp
          $algExpr1:algExpr) =>
        algExpr.unaryAlgebraOperation
          (unAlgOp.toType op) (toType algExpr1)

      | `(algExpr|
          $op:binAlgOp
          [$algExpr1:algExpr,
          $algExpr2:algExpr]) =>
        algExpr.binaryAlgebraOperation
          (binAlgOp.toType op) (toType algExpr1) (toType algExpr2)

      | _ => algExpr.number (1:Int) -- unreachable

  /--
  Gets the required variables for the algebra expression.

  Only needed for cardinal expression here.
  -/
  def getReqVariables
    (ae : algExpr)
    : List (String) := Id.run do
      match ae with
        | algExpr.number _ => []
        | algExpr.cardExpr ce => ce.getReqVariables
        | algExpr.unaryAlgebraOperation _ ae => ae.getReqVariables
        | algExpr.binaryAlgebraOperation _ ae1 ae2 =>
            ae1.getReqVariables ++  ae2.getReqVariables

end Shared.algExpr
