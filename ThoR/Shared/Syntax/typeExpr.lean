/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.mult
import ThoR.Shared.Syntax.arrowOp

open ThoR
open Lean

namespace Shared

  /--
  This inductive type represents a typeExpression
  -/
  inductive typeExpr
    | arrowExpr : (arrowExpr : arrowOp) → typeExpr
    | multExpr :
        (m : mult) →
        (expr : expr) →
        typeExpr
    | relExpr :
        (expr : expr) →
        typeExpr
  deriving Repr

  /--
  This syntax represents a typeExpression
  -/
  declare_syntax_cat typeExpr
  syntax arrowOp : typeExpr
  syntax expr : typeExpr
  syntax mult expr : typeExpr

  instance : ToString typeExpr where
    toString : typeExpr -> String
      | typeExpr.arrowExpr ae => ae.toString
      | typeExpr.multExpr m e => (m.toString) ++ " " ++ (e.toString)
      | typeExpr.relExpr e => e.toString

  instance : BEq typeExpr where
    beq : typeExpr -> typeExpr -> Bool
      | typeExpr.arrowExpr ae1, typeExpr.arrowExpr ae2 => ae1 == ae2
      | typeExpr.multExpr m1 e1, typeExpr.multExpr m2 e2 => (m1 == m2) && (e1 == e2)
      | typeExpr.relExpr e1, typeExpr.relExpr e2 => e1 == e2
      | _, _ => false
  namespace typeExpr

  instance : Inhabited typeExpr where
    default := typeExpr.relExpr default

    /--
    Generates a string representation of the type
    -/
    def toString (te : typeExpr) : String := s!"{te}"

    /--
    Generates syntax corosponding to the type
    -/
    def toSyntax
      (te: typeExpr)
      (blockName : Name)
      : TSyntax `typeExpr := Unhygienic.run do
        match te with
          | typeExpr.arrowExpr ae => `(typeExpr| $(ae.toSyntax blockName):arrowOp)
          | typeExpr.multExpr m e => `(typeExpr| $(m.toSyntax):mult $(e.toSyntax blockName):expr)
          | typeExpr.relExpr e => `(typeExpr| $(e.toSyntax blockName):expr)

    /--
    Generates a Lean term corosponding with the type

    to be called from an alloy block
    -/
    def toTermFromBlock
      (te : Shared.typeExpr)
      (blockName : Name)
      : TSyntax `term := Unhygienic.run do
        match te with
          | Shared.typeExpr.arrowExpr ae =>
            `($(mkIdent ``ThoR.Rel) $(ae.toTermFromBlock blockName))

          | Shared.typeExpr.multExpr m e =>
            `($(mkIdent ``ThoR.Rel)
              ($(mkIdent ``RelType.mk.unary_rel)
                $(m.toTerm) $(e.toTermFromBlock blockName)))
          | Shared.typeExpr.relExpr e =>
            `($(mkIdent ``ThoR.Rel)
              ($(mkIdent ``RelType.mk.rel)
                $(e.toTermFromBlock blockName)))

    /--
    Generates a Lean term corresponding to the type

    to be called from outside of an alloy block
    -/
    def toTermOutsideBlock
      (te : Shared.typeExpr)
      : TSyntax `term := Unhygienic.run do
        match te with
          | Shared.typeExpr.arrowExpr ae =>
            `($(mkIdent ``ThoR.Rel) $(ae.toTermOutsideBlock))

          | Shared.typeExpr.multExpr m e =>
            `($(mkIdent ``ThoR.Rel)
              ($(mkIdent ``RelType.mk.unary_rel)
                $(m.toTerm) $(e.toTermOutsideBlock)))

          | Shared.typeExpr.relExpr e =>
            `($(mkIdent ``ThoR.Rel)
              ($(mkIdent ``RelType.mk.rel)
                $(e.toTermOutsideBlock)))

    /--
    changes a string expr in the type expression to a string rb expression
    -/
    def toStringRb (te: typeExpr) : typeExpr :=
      match te with
        | typeExpr.relExpr e => typeExpr.relExpr (e.toStringRb)
        | typeExpr.multExpr m e => typeExpr.multExpr m (e.toStringRb)
        | typeExpr.arrowExpr ae => typeExpr.arrowExpr (ae.toStringRb)

    /--
    Parses the given syntax to the type
    -/
    def toType
      (te : TSyntax `typeExpr)
      : typeExpr :=
      match te with
        | `(typeExpr | $e:expr) =>
          typeExpr.relExpr (expr.toType e)

        | `(typeExpr | $m:mult $e:expr) =>
          typeExpr.multExpr (mult.toType m) (expr.toType e)

        | `(typeExpr | $arrowExpr:arrowOp) =>
          typeExpr.arrowExpr (arrowOp.toType arrowExpr)

        | _ => typeExpr.multExpr
          mult.one (expr.const constant.none) -- unreachable

    /--
    Gets the required variables for type expression to work
    -/
    def getReqVariables (te : typeExpr) : List (String) :=
      match te with
        | typeExpr.arrowExpr ae => ae.getReqVariables
        | typeExpr.multExpr _ e => e.getReqVariables
        | typeExpr.relExpr e => e.getReqVariables

    def getStringExpr (te:typeExpr) : String :=
      match te with
        | typeExpr.multExpr _ e => e.getStringExpr
        | typeExpr.relExpr e => e.getStringExpr
        | typeExpr.arrowExpr _ => default

    def getRelationCalls
      (te: typeExpr)
      (relationNames : List (String))
      : List (String) := Id.run do
        match te with
          | arrowExpr ae =>
              (ae.getRelationCalls relationNames)
          | multExpr _ e =>
              (e.getRelationCalls relationNames)
          | relExpr e =>
              (e.getRelationCalls relationNames)

    def replaceRelationCalls
      (te: typeExpr)
      (relationNames :List (String))
      (replacementNames :List (String))
      : typeExpr := Id.run do
        match te with
          | arrowExpr ae =>
            arrowExpr
              (ae.replaceRelationCalls relationNames replacementNames)
          | multExpr m e =>
            multExpr
              m
              (e.replaceRelationCalls relationNames replacementNames)
          | relExpr e =>
            relExpr
              (e.replaceRelationCalls relationNames replacementNames)

  end typeExpr

end Shared
