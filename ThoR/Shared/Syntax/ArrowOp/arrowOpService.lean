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
  Gets all calls to the `callableVariables` which includes signatures and relations

  The result is a list of the call (in string from) and a (possibly empty) list
  of the concrete possible called variables (in form of varDecls). If the inner
  list contains more than one varDecl, called variable is ambiguous and could
  be either.
  -/
  def getCalledVariables
    (ao : arrowOp)
    (callableVariables : List (varDecl))
    : Except String (List (String × List (varDecl))) := do
      match ao with
        | multArrowOpExpr e1 _ _ e2 =>
          let e1_calls ← (e1.getCalledVariables callableVariables)
          let e2_calls ← (e2.getCalledVariables callableVariables)
          return e1_calls ++ e2_calls

        | multArrowOpExprLeft e _ _ ao =>
          let e_calls ← (e.getCalledVariables callableVariables)
          let ao_calls ← (ao.getCalledVariables callableVariables)
          return e_calls ++ ao_calls

        | multArrowOpExprRight ao _ _ e =>
          let ao_calls ← (ao.getCalledVariables callableVariables)
          let e_calls ← (e.getCalledVariables callableVariables)
          return ao_calls ++ e_calls

        | multArrowOp ao1 _ _ ao2 =>
          let ao1_calls ← (ao1.getCalledVariables callableVariables)
          let ao2_calls ← (ao2.getCalledVariables callableVariables)
          return ao1_calls ++ ao2_calls

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

  /--
  If possible replace domain restrictions with relations.

  This is only possible, if the relation is restricted from the
  signature it is defined in.

  E.g. m1/a<:r gets simplified to the relation r IF r is a relation of a
  -/
  def simplifyDomainRestrictions
    (ao : arrowOp)
    (st : SymbolTable)
    : arrowOp :=
      match ao with
        | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
          arrowOp.multArrowOpExpr
            (e1.simplifyDomainRestrictions st)
            m1 m2
            (e2.simplifyDomainRestrictions st)

        | arrowOp.multArrowOpExprLeft e1 m1 m2 ae2 =>
          arrowOp.multArrowOpExprLeft
            (e1.simplifyDomainRestrictions st)
            m1 m2
            (ae2.simplifyDomainRestrictions st)

        | arrowOp.multArrowOpExprRight ae1 m1 m2 e2 =>
          arrowOp.multArrowOpExprRight
            (ae1.simplifyDomainRestrictions st)
            m1 m2
            (e2.simplifyDomainRestrictions st)

        | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
          arrowOp.multArrowOp
            (ae1.simplifyDomainRestrictions st)
            m1 m2
            (ae2.simplifyDomainRestrictions st)

  def insertModuleVariables
    (ao : arrowOp)
    (moduleVariables openVariables : List (String))
    : arrowOp :=
    match ao with
      | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
        arrowOp.multArrowOpExpr
          (e1.insertModuleVariables moduleVariables openVariables)
          m1 m2
          (e2.insertModuleVariables moduleVariables openVariables)

      | arrowOp.multArrowOpExprLeft e1 m1 m2 ae2 =>
        arrowOp.multArrowOpExprLeft
          (e1.insertModuleVariables moduleVariables openVariables)
          m1 m2
          (ae2.insertModuleVariables moduleVariables openVariables)

      | arrowOp.multArrowOpExprRight ae1 m1 m2 e2 =>
        arrowOp.multArrowOpExprRight
          (ae1.insertModuleVariables moduleVariables openVariables)
          m1 m2
          (e2.insertModuleVariables moduleVariables openVariables)

      | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
        arrowOp.multArrowOp
          (ae1.insertModuleVariables moduleVariables openVariables)
          m1 m2
          (ae2.insertModuleVariables moduleVariables openVariables)


  /--
  replaces calls to "this" (current module), with a call to the given module
  name.
  -/
  def replaceThisCalls
    (ao : arrowOp)
    (moduleName : String)
    : arrowOp :=
    match ao with
      | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
        arrowOp.multArrowOpExpr
          (e1.replaceThisCalls moduleName)
          m1 m2
          (e2.replaceThisCalls moduleName)

      | arrowOp.multArrowOpExprLeft e1 m1 m2 ae2 =>
        arrowOp.multArrowOpExprLeft
          (e1.replaceThisCalls moduleName)
          m1 m2
          (ae2.replaceThisCalls moduleName)

      | arrowOp.multArrowOpExprRight ae1 m1 m2 e2 =>
        arrowOp.multArrowOpExprRight
          (ae1.replaceThisCalls moduleName)
          m1 m2
          (e2.replaceThisCalls moduleName)

      | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
        arrowOp.multArrowOp
          (ae1.replaceThisCalls moduleName)
          m1 m2
          (ae2.replaceThisCalls moduleName)

end Shared.arrowOp
