/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Algebra
import ThoR.Shared.Syntax.Algebra.CardExpr.cardExprService
import ThoR.Alloy.Exceptions.NoMatchImplementedException

open Lean

namespace Shared.algExpr

  private def unhygienicUnfolder
    (input : Unhygienic (Term))
    : Term := Unhygienic.run do
    return ← input

  /--
  Generates a Lean term corosponding with the type
  -/
  def toTerm
  (ae : algExpr)
  (blockName : Name)
  : Except String Term := do
    match ae with
      | algExpr.number n =>
        return unhygienicUnfolder
          `($(Lean.Syntax.mkNumLit s!"{n.natAbs}"):num)

      | algExpr.cardExpr ce =>
        match ce with
          | cardExpr.cardExpression expr =>
            let eTerm ← expr.toTermFromBlock blockName
            return unhygienicUnfolder
              `(($(mkIdent ``ThoR.Card.card) $(eTerm)))

      | algExpr.unaryAlgebraOperation op ae =>
        let aeTerm ← ae.toTerm blockName
        return unhygienicUnfolder
          `(($(op.toTerm) $(aeTerm)))

      | algExpr.binaryAlgebraOperation op ae1 ae2 =>
        let ae1Term ← ae1.toTerm blockName
        let ae2Term ← ae2.toTerm blockName
        return unhygienicUnfolder
          `(($(op.toTerm) $(ae1Term) $(ae2Term)))

  def toTermOutsideBlock
  (ae : algExpr)
  : Except String Term := do
    match ae with
      | algExpr.number n =>
        return unhygienicUnfolder
          `($(Lean.Syntax.mkNumLit s!"{n.natAbs}"):num)

      | algExpr.cardExpr ce =>
        match ce with
          | cardExpr.cardExpression expr =>
            let eTerm ← expr.toTermOutsideBlock
            return unhygienicUnfolder
              `(($(mkIdent ``ThoR.Card.card) $(eTerm)))

      | algExpr.unaryAlgebraOperation op ae =>
        let aeTerm ← ae.toTermOutsideBlock
        return unhygienicUnfolder
          `(($(op.toTerm) $(aeTerm)))

      | algExpr.binaryAlgebraOperation op ae1 ae2 =>
        let ae1Term ← ae1.toTermOutsideBlock
        let ae2Term ← ae2.toTermOutsideBlock
        return unhygienicUnfolder
          `(($(op.toTerm) $(ae1Term) $(ae2Term)))

  /--
  Parses the given syntax to the type
  -/
  partial def toType
    (ae : AlgExpr)
    : Except String algExpr := do
      match ae with
        | `(algExpr| $number:num) =>
          return algExpr.number (number.getNat : Int)

        | `(algExpr| $ce:cardExpr) =>
          return algExpr.cardExpr (← cardExpr.toType ce)

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

        | syntx =>
          throwNoMatchImplemented "algExprService.toType" syntx

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
