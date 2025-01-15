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
import ThoR.Shared.Syntax.Relation.expr

open ThoR
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
  deriving Repr

  /--
  This syntax represents an arrowOp
  -/
  declare_syntax_cat arrowOp

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
    compares two arrowOps. returns bool if they are equal
    -/
    def compare (ae1 ae2 : arrowOp) : Bool :=
      match ae1, ae2 with
        | arrowOp.multArrowOpExpr e1 m1 m2 e2,
          arrowOp.multArrowOpExpr e3 m3 m4 e4 =>
          (e1.compare e3) && (m1 == m3)
            && (m2 == m4) && (e2.compare e4)

        | arrowOp.multArrowOpExprLeft e1 m1 m2 ao1,
          arrowOp.multArrowOpExprLeft e2 m3 m4 ao2 =>
          (e1.compare e2) && (m1 == m3)
            && (m2 == m4) && (ao1.compare ao2)

        | arrowOp.multArrowOpExprRight ao1 m1 m2 e1,
          arrowOp.multArrowOpExprRight ao2 m3 m4 e2 =>
          (ao1.compare ao2) && (m1 == m3)
            && (m2 == m4) && (e1.compare e2)

        | arrowOp.multArrowOp ao1 m1 m2 ao2,
          arrowOp.multArrowOp ao3 m3 m4 ao4 =>
          (ao1.compare ao3) && (m1 == m3)
            && (m2 == m4) && (ao2.compare ao4)

        | _, _ => false

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

    /--
    changes a string expr in the arrowOp to a string rb expression
    -/
    def toStringRb (ae : arrowOp) : arrowOp :=
      match ae with
        | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
          arrowOp.multArrowOpExpr (e1.toStringRb) m1 m2 (e2.toStringRb)

        | arrowOp.multArrowOpExprLeft e1 m1 m2 ae2 =>
          arrowOp.multArrowOpExprLeft (e1.toStringRb) m1 m2 (ae2.toStringRb)

        | arrowOp.multArrowOpExprRight ae1 m1 m2 e2 =>
          arrowOp.multArrowOpExprRight (ae1.toStringRb) m1 m2 (e2.toStringRb)

        | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
          arrowOp.multArrowOp (ae1.toStringRb) m1 m2 (ae2.toStringRb)

    instance : ToString arrowOp where
      toString : arrowOp -> String := fun ae => ae.toString

    instance : BEq arrowOp where
      beq : arrowOp -> arrowOp -> Bool := fun ae1 ae2 => ae1.compare ae2

    instance : Inhabited arrowOp where
      default :=
        arrowOp.multArrowOpExpr
          (expr.const constant.none)
          (mult.set)
          (mult.set)
          (expr.const constant.none)

    /--
    Generates syntax corosponding to the type
    -/
    def toSyntax
      (ao : arrowOp)
      (blockName : Name)
      : TSyntax `arrowOp := Unhygienic.run do
        match ao with
          | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
            `(arrowOp|
              $(e1.toSyntax blockName):expr
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(e2.toSyntax blockName):expr)

          | arrowOp.multArrowOpExprLeft e1 m1 m2 ae2 =>
            `(arrowOp|
              $(e1.toSyntax blockName):expr
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(ae2.toSyntax blockName):arrowOp)

          | arrowOp.multArrowOpExprRight ae1 m1 m2 e2 =>
            `(arrowOp|
              $(ae1.toSyntax blockName):arrowOp
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(e2.toSyntax blockName):expr)

          | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
            `(arrowOp|
              $(ae1.toSyntax blockName):arrowOp
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(ae2.toSyntax blockName):arrowOp)

    /--
    Generates a Lean term corosponding with the type

    this is to be calles from an alloy block to add the namespaces
    -/
    def toTermFromBlock
      (ao : Shared.arrowOp)
      (blockName : Name)
      : TSyntax `term := Unhygienic.run do

      match ao with
        | arrowOp.multArrowOpExpr (e1 : expr) (m1 : mult) (m2 : mult) (e2 : expr) =>
          `(
            $(mkIdent ``RelType.complex)
              ($(mkIdent ``ThoR.Rel.getType) ($(e1.toTermFromBlock blockName)))
              ($(m1.toTerm))
              ($(m2.toTerm))
              ($(mkIdent ``ThoR.Rel.getType) ($(e2.toTermFromBlock blockName)))
          )
        | arrowOp.multArrowOpExprLeft (e1 : expr) (m1 : mult) (m2 : mult) (ae2 : arrowOp) =>
          `(
            $(mkIdent ``RelType.complex)
              ($(mkIdent ``ThoR.Rel.getType) ($(e1.toTermFromBlock blockName)))
              ($(m1.toTerm))
              ($(m2.toTerm))
              $(ae2.toTermFromBlock blockName)
          )
        | arrowOp.multArrowOpExprRight (ae1 : arrowOp) (m1 : mult) (m2 : mult) (e2 : expr) =>
          `(
            $(mkIdent ``RelType.complex)
              $(ae1.toTermFromBlock blockName)
              ($(m1.toTerm))
              ($(m2.toTerm))
              ($(mkIdent ``ThoR.Rel.getType) ($(e2.toTermFromBlock blockName)))
          )
        | arrowOp.multArrowOp (ae1 : arrowOp) (m1 : mult) (m2 : mult) (ae2 : arrowOp) =>
          `(
            $(mkIdent ``RelType.complex)
              $(ae1.toTermFromBlock blockName)
              ($(m1.toTerm))
              ($(m2.toTerm))
              $(ae2.toTermFromBlock blockName)
          )

    /--
    Generates a Lean term corosponding with the type

    this can be calles outside an alloy block and no namespaces are added
    -/
    def toTermOutsideBlock
      (ao : Shared.arrowOp)
      : TSyntax `term := Unhygienic.run do

      match ao with
        | arrowOp.multArrowOpExpr (e1 : expr) (m1 : mult) (m2 : mult) (e2 : expr) =>
          `(
            $(mkIdent ``RelType.complex)
              ($(mkIdent ``ThoR.Rel.getType) ($(e1.toTermOutsideBlock)))
              ($(m1.toTerm))
              ($(m2.toTerm))
              ($(mkIdent ``ThoR.Rel.getType) ($(e2.toTermOutsideBlock)))
          )
        | arrowOp.multArrowOpExprLeft (e1 : expr) (m1 : mult) (m2 : mult) (ae2 : arrowOp) =>
          `(
            $(mkIdent ``RelType.complex)
              ($(mkIdent ``ThoR.Rel.getType) ($(e1.toTermOutsideBlock)))
              ($(m1.toTerm))
              ($(m2.toTerm))
              $(ae2.toTermOutsideBlock)
          )
        | arrowOp.multArrowOpExprRight (ae1 : arrowOp) (m1 : mult) (m2 : mult) (e2 : expr) =>
          `(
            $(mkIdent ``RelType.complex)
              $(ae1.toTermOutsideBlock)
              ($(m1.toTerm))
              ($(m2.toTerm))
              ($(mkIdent ``ThoR.Rel.getType) ($(e2.toTermOutsideBlock)))
          )
        | arrowOp.multArrowOp (ae1 : arrowOp) (m1 : mult) (m2 : mult) (ae2 : arrowOp) =>
          `(
            $(mkIdent ``RelType.complex)
              $(ae1.toTermOutsideBlock)
              ($(m1.toTerm))
              ($(m2.toTerm))
              $(ae2.toTermOutsideBlock)
          )

    /--
    Parses the given syntax to the type
    -/
    partial def toType (op : TSyntax `arrowOp) : arrowOp :=
      match op with
        -- multArrowOpExpr
        | `(arrowOp| ($ae:arrowOp)) => toType ae
        -- multArrowOpExpr
        | `(arrowOp|
            $subArrowExpr1:expr
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:expr) =>
          arrowOp.multArrowOpExpr (expr.toType subArrowExpr1)
            (mult.fromOption mult1) (mult.fromOption mult2)
            (expr.toType subArrowExpr2)

        -- multArrowOpExprLeft
        | `(arrowOp|
            $subArrowExpr1:expr
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:arrowOp) =>
          arrowOp.multArrowOpExprLeft (expr.toType subArrowExpr1)
            (mult.fromOption mult1) (mult.fromOption mult2)
            (toType subArrowExpr2)

        --multArrowOpExprRight
        | `(arrowOp|
            $subArrowExpr1:arrowOp
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:expr) =>
          arrowOp.multArrowOpExprRight (toType subArrowExpr1)
            (mult.fromOption mult1) (mult.fromOption mult2)
            (expr.toType subArrowExpr2)

        --multArrowOp
        | `(arrowOp|
            $subArrowExpr1:arrowOp
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:arrowOp) =>
          arrowOp.multArrowOp (toType subArrowExpr1)
            (mult.fromOption mult1) (mult.fromOption mult2)
            (toType subArrowExpr2)

        | _ => arrowOp.multArrowOpExpr (expr.const constant.none)
            (mult.set) (mult.set)
            (expr.const constant.none) -- unreachable

    /--
    Gets the required variables for the arrowOp to work (as a term)
    -/
    def getReqVariables (ae : arrowOp) : List (String) :=
      match ae with
        | arrowOp.multArrowOpExpr e1 _ _ e2 => e1.getReqVariables ++ e2.getReqVariables
        | arrowOp.multArrowOpExprLeft e1 _ _ ae2 => e1.getReqVariables ++ ae2.getReqVariables
        | arrowOp.multArrowOpExprRight ae1 _ _ e2 => ae1.getReqVariables ++ e2.getReqVariables
        | arrowOp.multArrowOp ae1 _ _ ae2 => ae1.getReqVariables ++ ae2.getReqVariables

    /--
    returns all signatures that are called and also are in the
    given name list (signature names).

    note that giving the names is required, since you can't decide
    on syntax alone if something is a signature or a relation
    -/
    def getSignatureCalls
      (ao: arrowOp)
      (signatureNames : List (String))
      : List (String) := Id.run do
        match ao with
          | multArrowOpExpr e1 _ _ e2 =>
            (e1.getSignatureCalls signatureNames) ++
              (e2.getSignatureCalls signatureNames)

          | multArrowOpExprLeft e _ _ ao1 =>
            (e.getSignatureCalls signatureNames) ++
              (ao1.getSignatureCalls signatureNames)

          | multArrowOpExprRight ao1 _ _ e =>
            (ao1.getSignatureCalls signatureNames) ++
              (e.getSignatureCalls signatureNames)

          | multArrowOp ao1 _ _ ao2 =>
            (ao1.getSignatureCalls signatureNames) ++
              (ao2.getSignatureCalls signatureNames)

    def getRelationCalls
      (ao: arrowOp)
      (relationNames : List (String))
      : List (String) := Id.run do
        match ao with
          | multArrowOpExpr e1 _ _ e2 =>
            (e1.getRelationCalls relationNames) ++
              (e2.getRelationCalls relationNames)

          | multArrowOpExprLeft e _ _ ao1 =>
            (e.getRelationCalls relationNames) ++
              (ao1.getRelationCalls relationNames)

          | multArrowOpExprRight ao1 _ _ e =>
            (ao1.getRelationCalls relationNames) ++
              (e.getRelationCalls relationNames)

          | multArrowOp ao1 _ _ ao2 =>
            (ao1.getRelationCalls relationNames) ++
              (ao2.getRelationCalls relationNames)

  end arrowOp

end Shared
