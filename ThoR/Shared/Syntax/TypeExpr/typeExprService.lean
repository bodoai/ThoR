/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.ArrowOp.arrowOpService
import ThoR.Shared.Syntax.Mutuals.mutualsService

open Alloy ThoR
open Lean

namespace Shared.typeExpr

  private def unhygienicUnfolder
    (input : Unhygienic (Term))
    : Term := Unhygienic.run do
    return ← input

  /--
  Generates a Lean term corresponding to the RelType

  to be called from outside of an alloy block
  -/
  def toRelTypeTermOutsideBlock
    (te : Shared.typeExpr)
    : Except String Term := do
      match te with
        | Shared.typeExpr.arrowExpr ae =>
          return unhygienicUnfolder
            `($(← ae.toTermOutsideBlock))

        | Shared.typeExpr.multExpr m e =>
          return unhygienicUnfolder
            `(($(mkIdent ``RelType.mk.unary_rel)
                $(m.toTerm) $(← e.toTermOutsideBlock)))

        | Shared.typeExpr.relExpr e =>
          return unhygienicUnfolder
            `(($(mkIdent ``RelType.mk.rel)
                $(← e.toTermOutsideBlock)))

  /--
  Parses the given syntax to the type
  -/
  def toType
    (te : TypeExpr)
    : Except String typeExpr := do
      match te with
        | `(typeExpr | $e:expr) =>
          return typeExpr.relExpr (← expr.toType e)

        | `(typeExpr | $m:mult $e:expr) =>
          return typeExpr.multExpr (← mult.toType m) (← expr.toType e)

        | `(typeExpr | $arrowExpr:arrowOp) =>
          return typeExpr.arrowExpr (← arrowOp.toType arrowExpr)

        | syntx =>
          throw s!"No match implemented in \
          typeExprService.toType \
          for '{syntx}'"

  def isString
    | typeExpr.relExpr e => e.isString
    | typeExpr.multExpr _ e => e.isString
    | _ => false

  def getStringData
    | typeExpr.relExpr e => e.getStringData
    | typeExpr.multExpr _ e => e.getStringData
    | e => panic! s!"Tried to get String data from expr {e}"

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

  /--
  If possible replace domain restrictions with relations.

  This is only possible, if the relation is restricted from the
  signature it is defined in.

  E.g. m1/a<:r gets simplified to the relation r IF r is a relation of a
  -/
  def simplifyDomainRestrictions
    (te : typeExpr)
    (st : SymbolTable)
    : typeExpr :=
      match te with
        | arrowExpr ae =>
          arrowExpr (ae.simplifyDomainRestrictions st)
        | multExpr m e =>
          multExpr m (e.simplifyDomainRestrictions st)
        | relExpr e =>
          relExpr (e.simplifyDomainRestrictions st)

  def insertModuleVariables
    (te : typeExpr)
    (moduleVariables openVariables : List (String))
    : typeExpr :=
      match te with
        | arrowExpr ae =>
          arrowExpr (ae.insertModuleVariables moduleVariables openVariables)
        | multExpr m e =>
          multExpr m (e.insertModuleVariables moduleVariables openVariables)
        | relExpr e =>
          relExpr (e.insertModuleVariables moduleVariables openVariables)

  /--
  replaces calls to "this" (current module), with a call to the given module
  name.
  -/
  def replaceThisCalls
    (te : typeExpr)
    (moduleName : String)
    : typeExpr :=
    match te with
      | arrowExpr ae =>
        arrowExpr (ae.replaceThisCalls moduleName)
      | multExpr m e =>
        multExpr m (e.replaceThisCalls moduleName)
      | relExpr e =>
        relExpr (e.replaceThisCalls moduleName)

  def getFunctionCalls
    (te : typeExpr)
    (callableFunctions : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String
      (List (commandDecl × List (expr × List (String × List (varDecl))))) := do
      match te with
      | arrowExpr ae =>
        ae.getFunctionCalls callableFunctions callableVariables
      | multExpr _ e =>
        e.getFunctionCalls callableFunctions callableVariables
      | relExpr e =>
        e.getFunctionCalls callableFunctions callableVariables

end Shared.typeExpr
