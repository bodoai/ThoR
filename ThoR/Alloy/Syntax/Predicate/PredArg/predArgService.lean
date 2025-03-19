/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Predicate.PredArg.predArg
import ThoR.Shared.Syntax.Relation.Expr.exprService

open Lean Shared

namespace Alloy.predArg

  /--
  Creates a predicate argument from the given parameters
  -/
  def create
    (disjunction:Bool)
    (names: Syntax.TSepArray `ident ",")
    (e: Expression)
    : predArg := Id.run do

    let names := (names.getElems.map fun (elem) => elem.getId.toString).toList
    let e := (expr.toType e)

    return {
      disjunction := disjunction
      names:= names
      expression := e
    }

  /--
  Parses the given syntax to a predArg if possible
  -/
  def toType (arg : PredArg) : predArg :=
    match arg with
      | `(predArg| disj $names:ident,* : $expression:expr) =>
        create true names expression

      | `(predArg| $names:ident,* : $expression:expr) =>
        create False names expression

      | _ => {
          disjunction := false
          expression := expr.const constant.none
          names:= ["panic"]
        } -- unreachable

  def simplifyDomainRestrictions
    (pa : predArg)
    (st : SymbolTable)
    : predArg :=
      {pa with expression := pa.expression.simplifyDomainRestrictions st}

  def insertModuleVariables
    (pa : predArg)
    (moduleVariables openVariables : List (String))
    : predArg :=
    {pa with expression :=
      pa.expression.insertModuleVariables moduleVariables openVariables}

  def replaceThisCalls
    (pa : predArg)
    (moduleName : String)
    : predArg :=
    {pa with expression :=
      pa.expression.replaceThisCalls moduleName}

  def getFunctionCalls
    (pa : predArg)
    (callableFunctions : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String
      (List (commandDecl × List (Shared.expr × List (String × List (varDecl))))) := do
    pa.expression.getFunctionCalls callableFunctions callableVariables

end Alloy.predArg
