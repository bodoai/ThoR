/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.Algebra.unAlgOp
import ThoR.Shared.Syntax.Algebra.binAlgOp
import ThoR.Shared.Syntax.Algebra.cardExpr
import ThoR.Shared.Syntax.baseType

open Lean

namespace Shared

  /--
  This inductive type represents an algebra expression
  -/
  inductive algExpr
    | number : (num : Int) → algExpr
    | cardExpr : (cardEx : cardExpr) → algExpr
    | unaryAlgebraOperation :
      (operator : unAlgOp) →
      (algExpr1 : algExpr) →
      algExpr
    | binaryAlgebraOperation :
      (operator : binAlgOp) →
      (algExpr1 : algExpr) →
      (algExpr2 : algExpr) →
      algExpr
  deriving Repr

  /--
  This syntax represents an algebra expression
  -/
  declare_syntax_cat algExpr
  syntax num : algExpr
  syntax cardExpr : algExpr
  syntax unAlgOp algExpr : algExpr
  syntax binAlgOp "[" algExpr "," algExpr "]" : algExpr

  namespace algExpr

    /--
    Generates a string representation of the type
    -/
    def toString (ae : algExpr) : String :=
      match ae with
        | algExpr.number n => ToString.toString n
        | algExpr.cardExpr ce => ce.toString
        | algExpr.unaryAlgebraOperation op ae => s!"{op} {toString ae}"
        | algExpr.binaryAlgebraOperation op ae1 ae2 =>
          s!"{op} [{toString ae1}, {toString ae2}]"

    instance : ToString algExpr where
      toString := toString

    instance : Inhabited algExpr where
      default := algExpr.number (1:Int)

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm
    (ae : algExpr)
    : TSyntax `term := Unhygienic.run do

      match ae with
        | algExpr.number n => `($(Lean.Syntax.mkNumLit s!"{n.natAbs}"):num)
        | algExpr.cardExpr _ =>
          `((@$(mkIdent ``ThoR.Card.card) $(baseType.getIdent) _))
        | algExpr.unaryAlgebraOperation op ae => `(($(op.toTerm) $(ae.toTerm)))
        | algExpr.binaryAlgebraOperation op ae1 ae2 =>
          `(($(op.toTerm) $(ae1.toTerm) $(ae2.toTerm)))

    /--
    Parses the given syntax to the type
    -/
    partial def toType (ae : TSyntax `algExpr) : algExpr :=
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

  end algExpr

end Shared
