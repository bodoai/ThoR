/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.ArrowOp.arrowOp
import ThoR.Shared.Syntax.Relation.Expr.exprService

open Alloy ThoR
open Lean

namespace Shared.arrowOp

  /--
  Replaces all calls to the callables from the List `callables`
  with their respective replacement
  in the given arrowOp `ao`
  -/
  def replaceCalls
    (ao: arrowOp)
    (callables :List (varDecl))
    : arrowOp :=
      match ao with
        | multArrowOpExpr e1 m1 m2 e2 =>
          multArrowOpExpr
            (e1.replaceCalls callables)
            m1
            m2
            (e2.replaceCalls callables)

        | multArrowOpExprLeft e m1 m2 ao1 =>
          multArrowOpExprLeft
            (e.replaceCalls callables)
            m1
            m2
            (ao1.replaceCalls callables)

        | multArrowOpExprRight ao1 m1 m2 e =>
          multArrowOpExprRight
            (ao1.replaceCalls callables)
            m1
            m2
            (e.replaceCalls callables)

        | multArrowOp ao1 m1 m2 ao2 =>
          multArrowOp
            (ao1.replaceCalls callables)
            m1
            m2
            (ao2.replaceCalls callables)

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
    (moduleName : String := default)
    : List (String) := Id.run do
      match ao with
        | multArrowOpExpr e1 _ _ e2 =>
          (e1.getSignatureCalls signatureNames moduleName) ++
            (e2.getSignatureCalls signatureNames moduleName)

        | multArrowOpExprLeft e _ _ ao1 =>
          (e.getSignatureCalls signatureNames moduleName) ++
            (ao1.getSignatureCalls signatureNames moduleName)

        | multArrowOpExprRight ao1 _ _ e =>
          (ao1.getSignatureCalls signatureNames moduleName) ++
            (e.getSignatureCalls signatureNames moduleName)

        | multArrowOp ao1 _ _ ao2 =>
          (ao1.getSignatureCalls signatureNames moduleName) ++
            (ao2.getSignatureCalls signatureNames moduleName)

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

end Shared.arrowOp
