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



  def getStringExpr (te:typeExpr) : String :=
    match te with
      | typeExpr.multExpr _ e => e.getStringExpr
      | typeExpr.relExpr e => e.getStringExpr
      | typeExpr.arrowExpr _ => default

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
