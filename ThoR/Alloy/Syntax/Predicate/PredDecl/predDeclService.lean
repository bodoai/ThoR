/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Predicate.PredDecl.predDecl
import ThoR.Alloy.Syntax.Predicate.PredArg.predArgService
import ThoR.Shared.Syntax.Formula.formulaService

import ThoR.Alloy.Exceptions.NoMatchImplementedException

open Lean Shared

namespace Alloy.predDecl

  /--
  Gets the required definitions for the predicate declaration to work
  -/
  def getReqDefinitions
    (pd : predDecl)
    : List (String) := Id.run do
      let mut result : List (String) := []

      for form in pd.forms do
        result := result ++ form.getReqDefinitions

      return result

  /--
  Gets the required variables for the predicate declaration to work
  -/
  def getReqVariables
    (pd : predDecl)
    : List (String) := Id.run do
      let mut result : List (String) := []

      for arg in pd.args do
        result := result ++ arg.expression.getReqVariables

      for form in pd.forms do
        result := result ++ form.getReqVariables

      return result

  /--
  Creates a predicate declaration with arguments
  -/
  def createWithArgs
    (name : Name)
    (input_arguments : Syntax.TSepArray `predArg ",")
    (forms : TSyntaxArray `formula)
    : Except String predDecl := do

    let mut arguments : List (predArg) := []
    for argument in input_arguments.getElems do
      arguments := arguments.concat (← predArg.toType argument)

    let mut forms_typed := []
    for f in forms do
      forms_typed := forms_typed.concat (← formula.toType f)

    return {
      name := name.toString
      args := arguments
      forms := forms_typed
    }

  /--
  Creates a predicate declaration without arguments
  -/
  def createWithoutArgs
    (name : Name)
    (forms : TSyntaxArray `formula)
    : Except String predDecl := do

    let mut forms_typed := []
    for f in forms do
      forms_typed := forms_typed.concat (← formula.toType f)

    return {
      name := name.toString
      args := []
      forms := forms_typed
    }

  /--
  Parses te given syntax to a structure of predDecl if possible
  -/
  def toType
    (pd : PredDecl)
    : Except String predDecl := do
      match pd with
        -- pred declaration with args
        | `(predDecl| pred $name:extendedIdent ($args:predArg,*) {
            $forms:formula*
          }) =>
            return ← predDecl.createWithArgs (extendedIdent.toName name) args forms

        | `(predDecl| pred $name:extendedIdent [$args:predArg,*] {
            $forms:formula*
          }) =>
            return ← predDecl.createWithArgs (extendedIdent.toName name) args forms

        -- pred declaration without args
        | `(predDecl| pred $name:extendedIdent {
            $forms:formula*
          }) =>
            return ← predDecl.createWithoutArgs (extendedIdent.toName name) forms

        | syntx =>
          throwNoMatchImplemented "predDeclService.toType" syntx

  def simplifyDomainRestrictions
    (pd : predDecl)
    (st : SymbolTable)
    : predDecl :=
    let args := pd.args.map fun arg => arg.simplifyDomainRestrictions st
    let forms := pd.forms.map fun f => f.simplifyDomainRestrictions st
    { pd with args := args, forms := forms}

  def insertModuleVariables
    (pd : predDecl)
    (moduleVariables openVariables : List (String))
    : predDecl :=
    let args := pd.args.map fun arg =>
      arg.insertModuleVariables moduleVariables openVariables
    let forms :=
      pd.forms.map fun f => f.insertModuleVariables moduleVariables openVariables
    { pd with args := args, forms := forms}

  def replaceThisCalls
    (pd : predDecl)
    (moduleName : String)
    : predDecl :=
    let args := pd.args.map fun arg =>
      arg.replaceThisCalls moduleName
    let forms :=
      pd.forms.map fun f => f.replaceThisCalls moduleName
    { pd with args := args, forms := forms}

  def getFunctionCalls
    (pd : predDecl)
    (callableFunctions : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String
      (List (commandDecl × List (Shared.expr × List (String × List (varDecl))))) := do
      let mut result := []
      for form in pd.forms do
        result := result.append (← form.getFunctionCalls callableFunctions callableVariables)
      for arg in pd.args do
        result := result.append (← arg.getFunctionCalls callableFunctions callableVariables)

      return result

end Alloy.predDecl
