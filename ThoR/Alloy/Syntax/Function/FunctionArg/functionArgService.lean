/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Function.FunctionArg.functionArg
import ThoR.Shared.Syntax.TypeExpr.typeExprService

open Shared

namespace Alloy.functionArg

 /--
  Gets the required variables for the function argument to work
  -/
  def getReqVariables
    (fa : functionArg)
    : List (String) := fa.type.getReqVariables

  def toType
    (fa : FunctionArg)
    : Except String functionArg := do
    match fa with
      | `(functionArg | disj $names:ident,* : $type:typeExpr) =>
        return {
          disjunction := true,
          names := (names.getElems.map fun n => n.getId.toString).toList,
          type := (← typeExpr.toType type)
        }
      | `(functionArg | $names:ident,* : $type:typeExpr) =>
        return {
          disjunction := false,
          names := (names.getElems.map fun n => n.getId.toString).toList,
          type := (← typeExpr.toType type)
        }

      | syntx =>
        throw s!"No match implemented in functionArgService.toType for '{syntx}'"

  def simplifyDomainRestrictions
    (fa : functionArg)
    (st : SymbolTable)
    : functionArg :=
    { fa with type := fa.type.simplifyDomainRestrictions st }

  def insertModuleVariables
    (fa : functionArg)
    (moduleVariables openVariables : List (String))
    : functionArg :=
    { fa with type := fa.type.insertModuleVariables moduleVariables openVariables }

  def replaceThisCalls
    (fa : functionArg)
    (moduleName : String)
    : functionArg :=
    { fa with type := fa.type.replaceThisCalls moduleName}

end Alloy.functionArg
