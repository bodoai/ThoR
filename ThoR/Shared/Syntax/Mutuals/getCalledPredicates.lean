/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the mutual data structures-/
import ThoR.Shared.Syntax.Mutuals.mutuals

/- import the commandDecl data structure -/
import ThoR.Alloy.SymbolTable.CommandDecl.commandDecl

import ThoR.Shared.Syntax.Mutuals.getCalledVariables

open Alloy

namespace Shared
  mutual
    /--
    Gets all calls to the `callablePredicates`

    The result takes the form of a List of Tuples which contain called Predicates
    (as commandDecl) with the given arguments (as varDecl)
    -/
    partial def formula.getCalledPredicates
      (f : formula)
      (callablePredicates : List (commandDecl))
      (callableVariables : List (varDecl))
      : Except String (List (commandDecl × List (expr × List (String × List (varDecl))))) := do
        let callablePredicateNames := callablePredicates.map fun cp => cp.name

        match f with
          | formula.bracket f =>
            f.getCalledPredicates callablePredicates callableVariables

          | formula.string s =>
            if callablePredicateNames.contains s then
              let index := callablePredicateNames.indexOf s
              let calledPredicate := callablePredicates.get! index
              return [(calledPredicate, [])]
            else
              return []

          | formula.pred_with_args predicate_name predicate_arguments =>
            if callablePredicateNames.contains predicate_name then
              let index := callablePredicateNames.indexOf predicate_name
              let calledPredicate := callablePredicates.get! index

              let mut calledArgumentVariables := []
              let mut args_cp := []
              for arg in predicate_arguments do
                calledArgumentVariables :=
                  calledArgumentVariables.concat
                    (arg, (← arg.getCalledVariables callableVariables))

                args_cp :=
                  args_cp ++
                    (← arg.getCalledPredicates callablePredicates callableVariables)

              return [(calledPredicate, calledArgumentVariables)] ++ args_cp
            else
              return []

          | formula.unaryLogicOperation _ f =>
            f.getCalledPredicates callablePredicates callableVariables

          | formula.binaryLogicOperation _ f1 f2 =>
            let f1_calls ← (f1.getCalledPredicates callablePredicates callableVariables)
            let f2_calls ← (f2.getCalledPredicates callablePredicates callableVariables)
            return f1_calls ++ f2_calls

          | formula.tertiaryLogicOperation _ f1 f2 f3 =>
            let f1_calls ← (f1.getCalledPredicates callablePredicates callableVariables)
            let f2_calls ← (f2.getCalledPredicates callablePredicates callableVariables)
            let f3_calls ← (f3.getCalledPredicates callablePredicates callableVariables)
            return f1_calls ++ f2_calls ++ f3_calls

          | formula.quantification _ _ _ te f =>
            let mut result := []
            for form in f do
              result := result ++ (← form.getCalledPredicates callablePredicates callableVariables)
            let te_cp ← te.getCalledPredicates callablePredicates callableVariables
            return result ++ te_cp

          | formula.letDeclaration _ value body =>
            let value_cp ← value.getCalledPredicates callablePredicates callableVariables
            let mut body_cps := []
            for element in body do
              let calledPreds ← element.getCalledPredicates callablePredicates callableVariables
              body_cps := body_cps ++ calledPreds
            return body_cps ++ value_cp

          | formula.relationComarisonOperation _ expr1 expr2 =>
            let expr1_cp ←
              expr1.getCalledPredicates callablePredicates callableVariables
            let expr2_cp ←
              expr2.getCalledPredicates callablePredicates callableVariables
            return expr1_cp ++ expr2_cp

          | formula.algebraicComparisonOperation _ algExpr1 algExpr2 =>
            let algExpr1_cp ←
              algExpr1.getCalledPredicates callablePredicates callableVariables
            let algExpr2_cp ←
              algExpr2.getCalledPredicates callablePredicates callableVariables
            return algExpr1_cp ++ algExpr2_cp

          | formula.unaryRelBoolOperation _ expression =>
            return (← expression.getCalledPredicates
              callablePredicates callableVariables)

    /--
    Gets all calls to the `callablePredicates`

    The result takes the form of a List of Tuples which contain called Predicates
    (as commandDecl) with the given arguments (as varDecl)
    -/
    partial def expr.getCalledPredicates
      (e : expr)
      (callablePredicates : List (commandDecl))
      (callableVariables : List (varDecl))
      : Except String
        (List (commandDecl × List (expr × List (String × List (varDecl)))))
      := do
      match e with
        | expr.bracket e =>
          e.getCalledPredicates callablePredicates callableVariables

        | expr.ifElse condition thenBody elseBody =>
          let condition_cp ←
            condition.getCalledPredicates callablePredicates callableVariables
          let thenBody_cp ←
            thenBody.getCalledPredicates callablePredicates callableVariables
          let elseBody_cp ←
            elseBody.getCalledPredicates callablePredicates callableVariables
          return condition_cp ++ thenBody_cp ++ elseBody_cp

        | expr.dotjoin _ expr1 expr2 =>
          let expr1_cp ←
            expr1.getCalledPredicates callablePredicates callableVariables
          let expr2_cp ←
            expr2.getCalledPredicates callablePredicates callableVariables
          return expr1_cp ++ expr2_cp

        | expr.binaryRelOperation _ expr1 expr2 =>
          let expr1_cp ←
            expr1.getCalledPredicates callablePredicates callableVariables
          let expr2_cp ←
            expr2.getCalledPredicates callablePredicates callableVariables
          return expr1_cp ++ expr2_cp

        | expr.unaryRelOperation  _ expression =>
          return (← expression.getCalledPredicates
            callablePredicates callableVariables)

        | expr.function_call_with_args _ arguments =>
          let mut arguments_cp := []
          for argument in arguments do
            arguments_cp :=
              arguments_cp ++
              (← argument.getCalledPredicates callablePredicates callableVariables)
          return arguments_cp

        | expr.const _ => return []
        | expr.callFromOpen _ => return []
        | expr.string_rb _ => return []
        | expr.string _ => return []

    /--
    Gets all calls to the `callablePredicates`

    The result takes the form of a List of Tuples which contain called Predicates
    (as commandDecl) with the given arguments (as varDecl)
    -/
    partial def typeExpr.getCalledPredicates
      (te : typeExpr)
      (callablePredicates : List (commandDecl))
      (callableVariables : List (varDecl))
      : Except String
        (List (commandDecl × List (expr × List (String × List (varDecl)))))
      := do
        match te with
        | typeExpr.arrowExpr ae =>
          ae.getCalledPredicates callablePredicates callableVariables
        | typeExpr.multExpr _ e =>
          e.getCalledPredicates callablePredicates callableVariables
        | typeExpr.relExpr e =>
          e.getCalledPredicates callablePredicates callableVariables

    /--
    Gets all calls to the `callablePredicates`

    The result takes the form of a List of Tuples which contain called Predicates
    (as commandDecl) with the given arguments (as varDecl)
    -/
    partial def arrowOp.getCalledPredicates
    (ao : arrowOp)
    (callablePredicates : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String
      (List (commandDecl × List (expr × List (String × List (varDecl)))))
    := do
      match ao with
      | arrowOp.multArrowOpExpr e1 _ _ e2 =>
        let e1_cp ← e1.getCalledPredicates callablePredicates callableVariables
        let e2_cp ← e2.getCalledPredicates callablePredicates callableVariables
        return e1_cp ++ e2_cp

      | arrowOp.multArrowOpExprLeft e1 _ _ ae2 =>
        let e1_cp ← e1.getCalledPredicates callablePredicates callableVariables
        let ae2_cp ← ae2.getCalledPredicates callablePredicates callableVariables
        return e1_cp ++ ae2_cp

      | arrowOp.multArrowOpExprRight ae1 _ _ e2 =>
        let ae1_cp ← ae1.getCalledPredicates callablePredicates callableVariables
        let e2_cp ← e2.getCalledPredicates callablePredicates callableVariables
        return ae1_cp ++ e2_cp

      | arrowOp.multArrowOp ae1 _ _ ae2 =>
        let ae1_cp ← ae1.getCalledPredicates callablePredicates callableVariables
        let ae2_cp ← ae2.getCalledPredicates callablePredicates callableVariables
        return ae1_cp ++ ae2_cp

    /--
    Gets all calls to the `callablePredicates`

    The result takes the form of a List of Tuples which contain called Predicates
    (as commandDecl) with the given arguments (as varDecl)
    -/
    partial def algExpr.getCalledPredicates
    (ae : algExpr)
    (callablePredicates : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String
      (List (commandDecl × List (expr × List (String × List (varDecl)))))
    := do
      match ae with
        | algExpr.number _ => return []
        | algExpr.cardExpression e =>
          e.getCalledPredicates callablePredicates callableVariables

        | algExpr.unaryAlgebraOperation _ ae =>
          ae.getCalledPredicates callablePredicates callableVariables

        | algExpr.binaryAlgebraOperation _ ae1 ae2 =>
          let ae1_cp ← ae1.getCalledPredicates callablePredicates callableVariables
          let ae2_cp ← ae2.getCalledPredicates callablePredicates callableVariables
          return ae1_cp ++ ae2_cp
  end
end Shared
