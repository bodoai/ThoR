/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
An arrowOp ist an operation between relations (expr) or other arrow operations
(arrowOps) and mults (optional for the alloy user)

-/
import ThoR.Basic
import ThoR.Shared.Syntax.mult
import ThoR.Shared.Syntax.Relation.Expr.expr

open Lean
namespace Shared

  /--
  This inductive type represents an arrowOp
  -/
  inductive arrowOp
    | multArrowOpExpr :
        (e1 : expr) →
        (mult1 : mult) →
        (mult2 : mult) →
        (e2 : expr) →
        arrowOp
    | multArrowOpExprLeft :
        (e : expr) →
        (mult1 : mult) →
        (mult2 : mult) →
        (ao : arrowOp) →
        arrowOp
    | multArrowOpExprRight :
        (ao : arrowOp) →
        (mult1 : mult) →
        (mult2 : mult) →
        (e : expr) →
        arrowOp
    | multArrowOp :
        (ao1 : arrowOp) →
        (mult1 : mult) →
        (mult2 : mult) →
        (ao2 : arrowOp) →
        arrowOp
  deriving Repr, BEq

  /--
  This syntax represents an arrowOp
  -/
  declare_syntax_cat arrowOp
  abbrev ArrowOp := TSyntax `arrowOp

  /--
  This syntax defines the allowed arrows
  -/
  declare_syntax_cat allowedArrows
  syntax " -> " : allowedArrows
  syntax " → " : allowedArrows

-- a  set  →  set  a  set  →  set  a

  syntax "(" arrowOp ")" : arrowOp
  syntax expr
          (mult)? allowedArrows (mult)?
          expr : arrowOp
  syntax expr
          (mult)? allowedArrows (mult)?
          arrowOp : arrowOp
  syntax arrowOp
          (mult)? allowedArrows (mult)?
          expr : arrowOp
  syntax arrowOp
          (mult)? allowedArrows (mult)?
          arrowOp : arrowOp

  namespace arrowOp

    /--
    Generates a string representation of the type
    -/
    def toString (ae : arrowOp) : String :=
      match ae with
        | arrowOp.multArrowOpExpr ae1 m1 m2 ae2 =>
          (ae1.toString) ++ " " ++ (m1.toString)
          ++ " → " ++
          (m2.toString) ++ " " ++ (ae2.toString)

        | arrowOp.multArrowOpExprLeft ae1 m1 m2 ae2 =>
          (ae1.toString) ++ " " ++ (m1.toString)
          ++ " → " ++
          (m2.toString) ++ " " ++ (ae2.toString)

        | arrowOp.multArrowOpExprRight ae1 m1 m2 ae2 =>
          (ae1.toString) ++ " " ++ (m1.toString)
          ++ " → " ++
          (m2.toString) ++ " " ++ (ae2.toString)

        | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
          (ae1.toString) ++ " " ++ (m1.toString)
          ++ " → " ++
          (m2.toString) ++ " " ++ (ae2.toString)

    instance : ToString arrowOp where
      toString : arrowOp -> String := fun ae => ae.toString

    instance : Inhabited arrowOp where
      default :=
        arrowOp.multArrowOpExpr
          (expr.const constant.none)
          (mult.set)
          (mult.set)
          (expr.const constant.none)

  end arrowOp

end Shared
