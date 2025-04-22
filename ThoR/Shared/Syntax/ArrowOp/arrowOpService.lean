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

  private def unhygienicUnfolder
    (input : Unhygienic (Term))
    : Term := Unhygienic.run do
    return ← input
  /--
  Generates a Lean term corosponding with the type

  this is to be calles from an alloy block to add the namespaces
  -/
  def toTermFromBlock
    (ao : Shared.arrowOp)
    (blockName : Name)
    : Except String Term := do

    match ao with
      | arrowOp.multArrowOpExpr
        (e1 : expr) (m1 : mult) (m2 : mult) (e2 : expr) =>
        let e1Term ← e1.toTermFromBlock blockName
        let e2Term ← e2.toTermFromBlock blockName
        return unhygienicUnfolder
          `(
            $(mkIdent ``RelType.complex)
              ($(mkIdent ``ThoR.Rel.getType) ($(e1Term)))
              ($(m1.toTerm))
              ($(m2.toTerm))
              ($(mkIdent ``ThoR.Rel.getType) ($(e2Term)))
        )
      | arrowOp.multArrowOpExprLeft (e1 : expr) (m1 : mult) (m2 : mult) (ae2 : arrowOp) =>
        let e1Term ← e1.toTermFromBlock blockName
        let ae2Term ← ae2.toTermFromBlock blockName
        return unhygienicUnfolder
          `(
            $(mkIdent ``RelType.complex)
              ($(mkIdent ``ThoR.Rel.getType) ($(e1Term)))
              ($(m1.toTerm))
              ($(m2.toTerm))
              $(ae2Term)
        )
      | arrowOp.multArrowOpExprRight (ae1 : arrowOp) (m1 : mult) (m2 : mult) (e2 : expr) =>
        let ae1Term ← ae1.toTermFromBlock blockName
        let e2Term ← e2.toTermFromBlock blockName
        return unhygienicUnfolder
          `(
            $(mkIdent ``RelType.complex)
              $(ae1Term)
              ($(m1.toTerm))
              ($(m2.toTerm))
              ($(mkIdent ``ThoR.Rel.getType) ($(e2Term)))
          )
      | arrowOp.multArrowOp (ae1 : arrowOp) (m1 : mult) (m2 : mult) (ae2 : arrowOp) =>
        let ae1Term ← ae1.toTermFromBlock blockName
        let ae2Term ← ae2.toTermFromBlock blockName
        return unhygienicUnfolder
          `(
            $(mkIdent ``RelType.complex)
              $(ae1Term)
              ($(m1.toTerm))
              ($(m2.toTerm))
              $(ae2Term)
          )

  /--
  Parses the given syntax to the type
  -/
  partial def toType
    (op : ArrowOp)
    : Except String arrowOp := do
      match op with
        -- multArrowOpExpr
        | `(arrowOp| ($ae:arrowOp)) => return ← toType ae
        -- multArrowOpExpr
        | `(arrowOp|
            $subArrowExpr1:expr
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:expr) =>
          return arrowOp.multArrowOpExpr
            (← expr.toType subArrowExpr1)
            (← mult.fromOption mult1)
            (← mult.fromOption mult2)
            (← expr.toType subArrowExpr2)

        -- multArrowOpExprLeft
        | `(arrowOp|
            $subArrowExpr1:expr
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:arrowOp) =>
          return arrowOp.multArrowOpExprLeft
            (← expr.toType subArrowExpr1)
            (← mult.fromOption mult1)
            (← mult.fromOption mult2)
            (← toType subArrowExpr2)

        --multArrowOpExprRight
        | `(arrowOp|
            $subArrowExpr1:arrowOp
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:expr) =>
          return arrowOp.multArrowOpExprRight
            (← toType subArrowExpr1)
            (← mult.fromOption mult1)
            (← mult.fromOption mult2)
            (← expr.toType subArrowExpr2)

        --multArrowOp
        | `(arrowOp|
            $subArrowExpr1:arrowOp
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:arrowOp) =>
          return arrowOp.multArrowOp
            (← toType subArrowExpr1)
            (← mult.fromOption mult1)
            (← mult.fromOption mult2)
            (← toType subArrowExpr2)

        | syntx =>
            throw s!"No match implemented in \
            arrowOpService.toType \
            for '{syntx}'"

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

  def getFunctionCalls
    (ao : arrowOp)
    (callableFunctions : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String
      (List (commandDecl × List (expr × List (String × List (varDecl))))) := do
      match ao with
      | arrowOp.multArrowOpExpr e1 _ _ e2 =>
        let e1_cf ← e1.getFunctionCalls callableFunctions callableVariables
        let e2_cf ← e2.getFunctionCalls callableFunctions callableVariables
        return e1_cf ++ e2_cf

      | arrowOp.multArrowOpExprLeft e1 _ _ ae2 =>
        let e1_cf ← e1.getFunctionCalls callableFunctions callableVariables
        let ae2_cf ← ae2.getFunctionCalls callableFunctions callableVariables
        return e1_cf ++ ae2_cf

      | arrowOp.multArrowOpExprRight ae1 _ _ e2 =>
        let ae1_cf ← ae1.getFunctionCalls callableFunctions callableVariables
        let e2_cf ← e2.getFunctionCalls callableFunctions callableVariables
        return ae1_cf ++ e2_cf

      | arrowOp.multArrowOp ae1 _ _ ae2 =>
        let ae1_cf ← ae1.getFunctionCalls callableFunctions callableVariables
        let ae2_cf ← ae2.getFunctionCalls callableFunctions callableVariables
        return ae1_cf ++ ae2_cf

end Shared.arrowOp
