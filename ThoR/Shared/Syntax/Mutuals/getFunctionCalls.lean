/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the data structures-/
import ThoR.Shared.Syntax.Mutuals.mutuals

/- import the commandDecl data structure -/
import ThoR.Alloy.SymbolTable.CommandDecl.commandDecl

/- import the getCalledVariables function -/
import ThoR.Shared.Syntax.Mutuals.getCalledVariables

open Alloy

namespace Shared
  mutual
    /--
    Get all function calls that are present in the formula
    -/
    partial def formula.getFunctionCalls
      (f : formula)
      (callableFunctions : List (commandDecl))
      (callableVariables : List (varDecl))
      : Except String
        (List (commandDecl × List (expr × List (String × List (varDecl)))))
      := do
        match f with
          | formula.bracket f =>
            f.getFunctionCalls callableFunctions callableVariables

          | formula.pred_with_args _ arguments =>
            let mut functionCalls := []
            for argument in arguments do
              functionCalls :=
                functionCalls.append
                  (← argument.getFunctionCalls callableFunctions callableVariables)
            return functionCalls

          | formula.unaryRelBoolOperation _ e =>
            return ← e.getFunctionCalls callableFunctions callableVariables

          | formula.unaryLogicOperation _ f =>
            f.getFunctionCalls callableFunctions callableVariables

          | formula.binaryLogicOperation _ f1 f2 =>
            let f1_cf ← f1.getFunctionCalls callableFunctions callableVariables
            let f2_cf ← f2.getFunctionCalls callableFunctions callableVariables
            return f1_cf ++ f2_cf

          | formula.tertiaryLogicOperation _ f1 f2 f3 =>
            let f1_cf ← f1.getFunctionCalls callableFunctions callableVariables
            let f2_cf ← f2.getFunctionCalls callableFunctions callableVariables
            let f3_cf ← f3.getFunctionCalls callableFunctions callableVariables
            return f1_cf ++ f2_cf ++ f3_cf

          | formula.relationComarisonOperation _ e1 e2 =>
            let e1_cf ← e1.getFunctionCalls callableFunctions callableVariables
            let e2_cf ← e2.getFunctionCalls callableFunctions callableVariables
            return e1_cf ++ e2_cf

          | formula.quantification _ _ _ te formulas =>
            let mut f_cf := []
            for f in formulas do
              f_cf :=
                f_cf.append
                  (← f.getFunctionCalls callableFunctions callableVariables)

            let te_cf ← te.getFunctionCalls callableFunctions callableVariables

            return f_cf ++ te_cf

          | formula.letDeclaration _ value body =>
            let value_cf ←
              value.getFunctionCalls callableFunctions callableVariables

            let mut body_cf := []
            for f in body do
              body_cf :=
                body_cf.append
                  (← f.getFunctionCalls callableFunctions callableVariables)

            return value_cf ++ body_cf

          | formula.algebraicComparisonOperation _ ae1 ae2 =>
            let ae1_cf ← ae1.getFunctionCalls callableFunctions callableVariables
            let ae2_cf ← ae2.getFunctionCalls callableFunctions callableVariables
            return ae1_cf ++ ae2_cf

          | formula.string _ => return []

    /--
    Get all function calls that are present in the expr
    -/
    partial def expr.getFunctionCalls
      (e : expr)
      (callableFunctions : List (commandDecl))
      (callableVariables : List (varDecl))
      : Except String
        (List (commandDecl × List (expr × List (String × List (varDecl)))))
      := do
        match e with
          | expr.bracket e =>
            e.getFunctionCalls callableFunctions callableVariables

          | expr.string s =>
            let possibleFunctions :=
              callableFunctions.filter fun cf => cf.name == s

            if possibleFunctions.length > 1 then
              throw s!"Call to function {s} is ambigious. Could be \
              any of {possibleFunctions}"

            if possibleFunctions.isEmpty then return []

            let calledFunction := possibleFunctions.get! 0
            if !calledFunction.isFunction then
              throw s!"Tried to call the {calledFunction.commandType} \
              {calledFunction.name} as a function"

            return [(calledFunction, [])]

          | expr.function_call_with_args function_name arguments =>
            let possibleFunctions :=
              callableFunctions.filter fun cf => cf.name == function_name

            if possibleFunctions.length > 1 then
              throw s!"Call to function {function_name} is ambigious. Could be \
              any of {possibleFunctions}"

            if possibleFunctions.isEmpty then return []
            let calledFunction := possibleFunctions.get! 0

            if !calledFunction.isFunction then
              throw s!"Tried to call the {calledFunction.commandType} \
              {calledFunction.name} as a function"

            let mut calledArguments : List (String × List (varDecl)) := []
            for argument in arguments do
              calledArguments :=
                calledArguments.append
                  (← (argument.getCalledVariables callableVariables))

            return [(calledFunction, [(e , calledArguments)])]

          | expr.unaryRelOperation _ e =>
            e.getFunctionCalls callableFunctions callableVariables

          | expr.binaryRelOperation _ e1 e2 =>
            let e1_cf ← e1.getFunctionCalls callableFunctions callableVariables
            let e2_c2 ← e2.getFunctionCalls callableFunctions callableVariables
            return e1_cf ++ e2_c2

          | expr.dotjoin _ e1 e2 =>
            let e1_cf ← e1.getFunctionCalls callableFunctions callableVariables
            let e2_c2 ← e2.getFunctionCalls callableFunctions callableVariables
            return e1_cf ++ e2_c2

          | expr.ifElse condition thenBody elseBody =>
            let condition_cf ←
              condition.getFunctionCalls callableFunctions callableVariables
            let thenBody_cf ←
              thenBody.getFunctionCalls callableFunctions callableVariables
            let elseBody_cf ←
              elseBody.getFunctionCalls callableFunctions callableVariables

            return condition_cf ++ thenBody_cf ++ elseBody_cf

          | expr.callFromOpen _ => return [] -- possibly incorrect
          | expr.string_rb _ => return []
          | expr.const _ => return []

    /--
    Get all function calls that are present in the expr
    -/
    partial def typeExpr.getFunctionCalls
      (te : typeExpr)
      (callableFunctions : List (commandDecl))
      (callableVariables : List (varDecl))
      : Except String
        (List (commandDecl × List (expr × List (String × List (varDecl))))) := do
        match te with
        | typeExpr.arrowExpr ae =>
          ae.getFunctionCalls callableFunctions callableVariables
        | typeExpr.multExpr _ e =>
          e.getFunctionCalls callableFunctions callableVariables
        | typeExpr.relExpr e =>
          e.getFunctionCalls callableFunctions callableVariables

    /--
    Get all function calls that are present in the expr
    -/
    partial def arrowOp.getFunctionCalls
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

    /--
    Get all function calls that are present in the expr
    -/
    partial def algExpr.getFunctionCalls
      (ae : algExpr)
      (callableFunctions : List (commandDecl))
      (callableVariables : List (varDecl))
      : Except String
        (List (commandDecl × List (expr × List (String × List (varDecl))))) := do
      match ae with
        | algExpr.number _ => return []
        | algExpr.cardExpression e =>
          e.getFunctionCalls callableFunctions callableVariables

        | algExpr.unaryAlgebraOperation _ ae =>
          ae.getFunctionCalls callableFunctions callableVariables

        | algExpr.binaryAlgebraOperation _ ae1 ae2 =>
          let ae1_cf ← ae1.getFunctionCalls callableFunctions callableVariables
          let ae2_cf ← ae2.getFunctionCalls callableFunctions callableVariables
          return ae1_cf ++ ae2_cf

  end
end Shared
