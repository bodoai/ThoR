/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.ArrowOp.arrowOpService

open Alloy ThoR
open Lean

namespace Shared.typeExpr

  /--
  Replaces all calls to the callables from the List `callables`
  with their respective replacement
  in the given typeExpr `te`
  -/
  def replaceCalls
    (te: typeExpr)
    (callables : List (varDecl))
    : typeExpr := Id.run do
      match te with
        | arrowExpr ae =>
          arrowExpr
            (ae.replaceCalls callables)
        | multExpr m e =>
          multExpr
            m
            (e.replaceCalls callables)
        | relExpr e =>
          relExpr
            (e.replaceCalls callables)

  /--
  Generates syntax corosponding to the type
  -/
  def toSyntax
    (te: typeExpr)
    (blockName : Name)
    : TypeExpr := Unhygienic.run do
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
    : Term := Unhygienic.run do
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
    : Term := Unhygienic.run do
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
  Generates a Lean term corresponding to the RelType

  to be called from outside of an alloy block
  -/
  def toRelTypeTermOutsideBlock
    (te : Shared.typeExpr)
    : Term := Unhygienic.run do
      match te with
        | Shared.typeExpr.arrowExpr ae =>
          `($(ae.toTermOutsideBlock))

        | Shared.typeExpr.multExpr m e =>
          `(($(mkIdent ``RelType.mk.unary_rel)
              $(m.toTerm) $(e.toTermOutsideBlock)))

        | Shared.typeExpr.relExpr e =>
          `(($(mkIdent ``RelType.mk.rel)
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
    (te : TypeExpr)
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
  Gets all calls to the `callableVariables` which includes signatures and relations

  The result is a list of the call (in string from) and a (possibly empty) list
  of the concrete possible called variables (in form of varDecls). If the inner
  list contains more than one varDecl, called variable is ambiguous and could
  be either.
  -/
  def getCalledVariables
    (te : typeExpr)
    (callableVariables : List (varDecl))
    : Except String (List (String × List (varDecl))) :=
      match te with
        | arrowExpr ae =>
          (ae.getCalledVariables callableVariables)
        | multExpr _ e =>
          (e.getCalledVariables callableVariables)
        | relExpr e =>
          (e.getCalledVariables callableVariables)

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

end Shared.typeExpr
