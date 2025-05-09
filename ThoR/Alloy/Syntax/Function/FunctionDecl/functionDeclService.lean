/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Function.FunctionDecl.functionDecl
import ThoR.Alloy.Syntax.Function.FunctionArg.functionArgService
import ThoR.Alloy.Syntax.Function.FunctionIfDecl.functionIfDeclService
import ThoR.Shared.Syntax.Relation.Expr.exprService
import ThoR.Shared.Syntax.TypeExpr.typeExprService

import ThoR.Alloy.Exceptions.NoMatchImplementedException

open Lean Shared

namespace Alloy.functionDecl

  /--
  Gets the required variables for the function declaration to work
  -/
  def getReqVariables
    (fd : functionDecl)
    : List (String) :=
      fd.outputType.getReqVariables ++
      (fd.arguments.map fun argument => argument.getReqVariables).join ++
      (fd.expressions.map fun expression => expression.getReqVariables).join

  def getFunctionCalls
    (fd : functionDecl)
    (callableFunctions : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String
      (List (commandDecl × List (expr × List (String × List (varDecl))))) := do
      let mut result := []
      for expression in fd.expressions do
        result := result.append (← expression.getFunctionCalls callableFunctions callableVariables)
      return result
  /--
  Splits the input array intp a List of expr and a List of functionIfDelcs.
  Then returns both.
  -/
  private def splitFunExpressions
    (input : TSyntaxArray `exprOfFunIfDecl)
    : Except String (List expr × List functionIfDecl) := do
      let mut output := ([],[])
      for element in input do
        match element with
          | `(exprOfFunIfDecl|$e:expr) =>
            return ((output.1.concat (← expr.toType e)), output.2)
          | `(exprOfFunIfDecl|$fid:functionIfDecl) =>
            let fid_typed ← functionIfDecl.toType fid
            return (output.1, output.2.concat fid_typed)
          | syntx =>
            throwNoMatchImplemented "functionDeclService.splitFunExpressions" syntx
      return output

  /--
  Parses te given syntax to a structure of functionDecl if possible
  -/
  def toType
    (pd : FunctionDecl)
    : Except String functionDecl := do
      match pd with
        -- function declaration with [] arguments
        | `(functionDecl |
            fun $name:extendedIdent
            [$arguments:functionArg,*]
            : $outputType:typeExpr {
            $funExprs:exprOfFunIfDecl*
          }) =>

            let splittetExpressions ←
              (splitFunExpressions funExprs)

            let mut arguments_typed := []
            for argument in arguments.getElems do
              arguments_typed :=
                arguments_typed.concat (← functionArg.toType argument)

            return {
              name := (extendedIdent.toName name).toString,
              arguments := arguments_typed,
              outputType := ← typeExpr.toType outputType,
              expressions := splittetExpressions.1,
              ifExpressions := splittetExpressions.2
            }

        -- function declaration with () arguments
        | `(functionDecl |
            fun $name:extendedIdent
            ($arguments:functionArg,*)
            : $outputType:typeExpr {
            $funExprs:exprOfFunIfDecl*
          }) =>

            let splittetExpressions ←
              (splitFunExpressions funExprs)

            let mut arguments_typed := []
            for argument in arguments.getElems do
              arguments_typed :=
                arguments_typed.concat (← functionArg.toType argument)

            return {
              name := (extendedIdent.toName name).toString,
              arguments := arguments_typed,
              outputType := ← typeExpr.toType outputType,
              expressions := splittetExpressions.1,
              ifExpressions := splittetExpressions.2
            }

        -- function declaration without arguments
        | `(functionDecl |
            fun $name:extendedIdent
            : $outputType:typeExpr {
            $funExprs:exprOfFunIfDecl*
          }) =>

            let splittetExpressions ←
              (splitFunExpressions funExprs)

            return {
              name := (extendedIdent.toName name).toString,
              arguments := default,
              outputType := ← typeExpr.toType outputType,
              expressions := splittetExpressions.1,
              ifExpressions := splittetExpressions.2
            }

        | syntx =>
          throwNoMatchImplemented "functionDeclService.toType" syntx

  def simplifyDomainRestrictions
    (fd : functionDecl)
    (st : SymbolTable)
    : functionDecl :=
    {
      fd with
        arguments := fd.arguments.map fun argument => argument.simplifyDomainRestrictions st,
        outputType := fd.outputType.simplifyDomainRestrictions st,
        expressions := fd.expressions.map fun expression => expression.simplifyDomainRestrictions st
     }

  def insertModuleVariables
    (fd : functionDecl)
    (moduleVariables openVariables : List (String))
    : functionDecl :=
    {
      fd with
        arguments := fd.arguments.map fun argument => argument.insertModuleVariables moduleVariables openVariables,
        outputType := fd.outputType.insertModuleVariables moduleVariables openVariables,
        expressions := fd.expressions.map fun expression => expression.insertModuleVariables moduleVariables openVariables
    }

  def replaceThisCalls
    (fd : functionDecl)
    (moduleName : String)
    : functionDecl :=
    {
      fd with
        arguments := fd.arguments.map fun argument => argument.replaceThisCalls moduleName,
        outputType := fd.outputType.replaceThisCalls moduleName,
        expressions := fd.expressions.map fun expression => expression.replaceThisCalls moduleName
    }

end Alloy.functionDecl
