/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the mutual data structures-/
import ThoR.Shared.Syntax.Mutuals.mutuals

/- import data structure varDecl-/
import ThoR.Alloy.SymbolTable.VarDecl.varDecl

open Alloy

namespace Shared
  mutual
    /--
    Gets all calls to the `callableVariables` which includes signatures and relations.

    The result is a list of the call (in string from) and a (possibly empty) list
    of the concrete possible called variables (in form of varDecls). If the inner
    list contains more than one varDecl, called variable is ambiguous and could
    be either.
    -/
    partial def formula.getCalledVariables
      (f : formula)
      (callableVariables : List (varDecl))
      : Except String (List (String × List (varDecl))) := do
        match f with
          | formula.bracket f => f.getCalledVariables callableVariables
          | formula.pred_with_args _ predicate_arguments =>
            let mut result : List (String × List varDecl) := []
            for pa in predicate_arguments do
              result := result ++ (← pa.getCalledVariables callableVariables)
            return result

          | formula.unaryRelBoolOperation _ e =>
            (e.getCalledVariables callableVariables)

          | formula.unaryLogicOperation _ f =>
            (f.getCalledVariables callableVariables)

          | formula.binaryLogicOperation _ f1 f2 =>
            let f1_calls ← (f1.getCalledVariables callableVariables)
            let f2_calls ← (f2.getCalledVariables callableVariables)
            return f1_calls ++ f2_calls

          | formula.tertiaryLogicOperation _ f1 f2 f3 =>
            let f1_calls ← (f1.getCalledVariables callableVariables)
            let f2_calls ← (f2.getCalledVariables callableVariables)
            let f3_calls ← (f3.getCalledVariables callableVariables)
            return f1_calls ++ f2_calls ++ f3_calls

          | formula.relationComarisonOperation _ e1 e2 =>
            let e1_calls ← (e1.getCalledVariables callableVariables)
            let e2_calls ← (e2.getCalledVariables callableVariables)
            return e1_calls ++ e2_calls

          | formula.quantification _ _ names te f =>
            let typeExprRelCalls ← te.getCalledVariables callableVariables

            let quantVarDecls :=
              names.map fun n =>
                varDecl.mk
                  (name := n)
                  (isQuantor := true)
                  (isOpened := false)
                  (openedFrom := "this")
                  (isRelation := false)
                  (relationOf := default)
                  (type := te)
                  (requiredDecls := [])

            let mut result : List (String × List varDecl) := []
            for form in f do
              result := result ++ (← form.getCalledVariables (callableVariables ++ quantVarDecls))

            return typeExprRelCalls ++ result

          | formula.letDeclaration _ value body =>
            let value_cp ← value.getCalledVariables callableVariables
            let mut body_cps := []
            for element in body do
              let calledPreds ← element.getCalledVariables callableVariables
              body_cps := body_cps ++ calledPreds
            return body_cps ++ value_cp

          | formula.algebraicComparisonOperation _ ae1 ae2 =>
            let ae1_cv ← ae1.getCalledVariables callableVariables
            let ae2_cv ← ae2.getCalledVariables callableVariables
            return ae1_cv ++ ae2_cv

          | formula.string _ => return []

    /--
    Gets all calls to the `callableVariables` which includes signatures and
    relations

    The result is a list of the call (in string from) and a (possibly empty) list
    of the concrete possible called variables (in form of varDecls). If the inner
    list contains more than one varDecl, called variable is ambiguous and could
    be either.
    -/
    partial def expr.getCalledVariables
      (e : expr)
      (callableVariables : List (varDecl))
      /-
      If a relation is called from the right side of a dotjoin
      and the left side is a signature which contains the name
      of the relation, then you dont habe to specify the full name
      of the relation and it can become only a expr.string. To handle
      this case the following two parameters are needed
      -/
      (right_side_dotjoin : Bool := false)
      (left_side_dotjoin_variable : varDecl := default)
      : Except String (List (String × List (varDecl))) := do
        let callableVariableNames := (callableVariables.map fun cv => cv.name)

        match e with
        | expr.bracket e => e.getCalledVariables callableVariables
        | expr.string s =>

          -- the name does not corrospond to ANY callable variable
          let isCallable := callableVariableNames.contains s
          if !isCallable then return []

          let indices := callableVariableNames.indexesOf s

          -- there is only one variable with the give name
          if indices.length == 1 then
            let calledVariable := callableVariables.get! (indices.get! 0)
            return [(s,[calledVariable])]

          -- get possible variables
          let possibleCalledVariables := indices.foldl
            (fun result index => result.concat (callableVariables.get! index))
            []

          /-
          if there is not special dotjoin case, then return all possible
          variables. (The called variable is ambiguous)
          -/
          if !right_side_dotjoin then return [(s, possibleCalledVariables)]

          /-
          Left side must not be a relation
          -/
          if left_side_dotjoin_variable.isRelation then return [(s, possibleCalledVariables)]

          /-
          If the left side is a quantor, the type has to be atomic
          -/
          if left_side_dotjoin_variable.isQuantor then
            let type := left_side_dotjoin_variable.type
            let isAtomic := match type with
              | typeExpr.arrowExpr _ => false
              | _ => true

            if !isAtomic then return [(s, possibleCalledVariables)]

            let possibleSignatures :=
              callableVariables.filter
                fun cv =>
                  -- has to be a signature
                  !cv.isRelation &&
                  -- need the same type as the quantor
                  cv.type == type &&
                  -- must not be a quantor
                  !cv.isQuantor

            -- only one must remain
            if
              possibleSignatures.isEmpty ||
              possibleSignatures.length > 1
            then
              return [(s, possibleCalledVariables)]

            let signature := (possibleSignatures.get! 0)

            let calledVariable :=
              callableVariables.filter fun cv =>
            -- has to be a relation
              cv.isRelation &&

              -- has to be a relation of the quantorType
              cv.relationOf == signature.relationOf &&

              (cv.isOpened == signature.isOpened &&
              cv.openedFrom == signature.openedFrom)

            return [(s, calledVariable)]

          -- if left side is signature (not quantor)
          else
            let calledVariable :=
              callableVariables.filter fun cv =>
            -- has to be a relation
              cv.isRelation &&

              -- has to be a relation of the signature type
              cv.relationOf == left_side_dotjoin_variable.name &&

              (cv.isOpened == left_side_dotjoin_variable.isOpened &&
              cv.openedFrom == left_side_dotjoin_variable.openedFrom)

            return [(s, calledVariable)]

        | expr.callFromOpen sn =>
          let fullName := sn.representedNamespace.getId.toString.replace "." "/"
          let components := sn.representedNamespace.getId.components

          let calledVariableName := components.getLast!

          let possibleCalledVariables :=
            callableVariables.filter
              fun cv =>
                cv.name == calledVariableName.toString

          -- if there is only one possible value
          if possibleCalledVariables.length == 1 then
            return [(fullName, possibleCalledVariables)]

          -- namespace if the called Variable is a signature
          let sigNamespace :=
            ((components.take (components.length - 1)).drop 1).foldl
              (fun result current => s!"{result}_{current}")
              (components.get! 0).toString

          -- alternate namespace if you use alloy style access
          let alternateSigNamespace :=
            ((components.take (components.length - 1)).drop (components.length - 2))

          -- the signature name if it is a relation
          let possibleSignatureName :=
            (components.get! (components.length - 2)).toString

          -- the namespace with the last element removed (assumend to be a sig name)
          let relNamespace :=
            ((components.take (components.length - 2)).drop 1).foldl
              (fun result current => s!"{result}_{current}")
              (components.get! 0).toString

          -- alternate namespace if you use alloy style access
          let alternateRelNamespace :=
            ((components.take (components.length - 2)).drop (components.length - 3))

          let calledVariables := possibleCalledVariables.filter
            fun pcv =>
              -- is either relation with correct sig name and namespace
              (
                pcv.isRelation &&
                pcv.relationOf == possibleSignatureName &&
                (
                  (pcv.openedFrom == relNamespace) ||
                  (
                    -- on the alternate namespace only the last element counts
                    !alternateRelNamespace.isEmpty &&
                    (
                      (pcv.openedFrom.splitOn "_").getLast! ==
                      alternateRelNamespace.getLast!.toString
                    )
                  ) ||
                  (
                    -- or this is implicit
                    (pcv.openedFrom == "this") &&
                    (pcv.isOpened == false) &&
                    (alternateRelNamespace.isEmpty)
                  )
                )
              ) ||
              -- or signature with correct namespace
              (
                !pcv.isRelation &&
                (
                  (pcv.openedFrom == sigNamespace) ||
                  (
                    -- on the alternate namespace only the last element counts
                    !alternateSigNamespace.isEmpty &&
                    (
                      (pcv.openedFrom.splitOn "_").getLast! ==
                      alternateSigNamespace.getLast!.toString
                    )
                  )
                )
              )

          return [(fullName, calledVariables)]

        | expr.unaryRelOperation _ e =>
          e.getCalledVariables callableVariables

        | expr.binaryRelOperation _ e1 e2 =>
          let e1_calls ← (e1.getCalledVariables callableVariables)
          let e2_calls ← (e2.getCalledVariables callableVariables)
          return e1_calls ++ e2_calls

        | expr.dotjoin _ e1 e2 =>
          /-TODO: As soons as it is possible to get the type of exprs then get it here-/
          /-Take the last possible expression -/
          let leftSideCalls ← e1.getCalledVariables callableVariables
          let e2' ← e2.getCalledVariables callableVariables
          let error_value := leftSideCalls ++ e2'

          if leftSideCalls.isEmpty then return error_value

          let leftSideLastCall := leftSideCalls.getLast!.2
          if leftSideLastCall.isEmpty then return error_value

          let leftSideLastVarDecl := leftSideLastCall.getLast!
          let rightSideCalls ←
            (e2.getCalledVariables
              (right_side_dotjoin := true)
              (left_side_dotjoin_variable := leftSideLastVarDecl)
              callableVariables)

          return leftSideCalls ++ rightSideCalls

        | expr.function_call_with_args _ arguments =>
          let mut cvs := []
          for argument in arguments do
            cvs := cvs.append (← argument.getCalledVariables callableVariables)
          return cvs

        | expr.ifElse condition thenBody elseBody =>
          let conditon_cv ← condition.getCalledVariables callableVariables
          let thenBody_cv ← thenBody.getCalledVariables callableVariables
          let elseBody_cv ← elseBody.getCalledVariables callableVariables

          return conditon_cv ++ thenBody_cv ++ elseBody_cv

        | expr.string_rb _ => return []
        | expr.const _ => return []

    /--
    Gets all calls to the `callableVariables` which includes signatures and relations

    The result is a list of the call (in string from) and a (possibly empty) list
    of the concrete possible called variables (in form of varDecls). If the inner
    list contains more than one varDecl, called variable is ambiguous and could
    be either.
    -/
    partial def typeExpr.getCalledVariables
      (te : typeExpr)
      (callableVariables : List (varDecl))
      : Except String (List (String × List (varDecl))) :=
        match te with
          | typeExpr.arrowExpr ae =>
            (ae.getCalledVariables callableVariables)
          | typeExpr.multExpr _ e =>
            (e.getCalledVariables callableVariables)
          | typeExpr.relExpr e =>
            (e.getCalledVariables callableVariables)

    /--
    Gets all calls to the `callableVariables` which includes signatures and relations

    The result is a list of the call (in string from) and a (possibly empty) list
    of the concrete possible called variables (in form of varDecls). If the inner
    list contains more than one varDecl, called variable is ambiguous and could
    be either.
    -/
    partial def arrowOp.getCalledVariables
      (ao : arrowOp)
      (callableVariables : List (varDecl))
      : Except String (List (String × List (varDecl))) := do
        match ao with
          | arrowOp.multArrowOpExpr e1 _ _ e2 =>
            let e1_calls ← (e1.getCalledVariables callableVariables)
            let e2_calls ← (e2.getCalledVariables callableVariables)
            return e1_calls ++ e2_calls

          | arrowOp.multArrowOpExprLeft e _ _ ao =>
            let e_calls ← (e.getCalledVariables callableVariables)
            let ao_calls ← (ao.getCalledVariables callableVariables)
            return e_calls ++ ao_calls

          | arrowOp.multArrowOpExprRight ao _ _ e =>
            let ao_calls ← (ao.getCalledVariables callableVariables)
            let e_calls ← (e.getCalledVariables callableVariables)
            return ao_calls ++ e_calls

          | arrowOp.multArrowOp ao1 _ _ ao2 =>
            let ao1_calls ← (ao1.getCalledVariables callableVariables)
            let ao2_calls ← (ao2.getCalledVariables callableVariables)
            return ao1_calls ++ ao2_calls

    /--
    Gets all calls to the `callableVariables` which includes signatures and relations

    The result is a list of the call (in string from) and a (possibly empty) list
    of the concrete possible called variables (in form of varDecls). If the inner
    list contains more than one varDecl, called variable is ambiguous and could
    be either.
    -/
    partial def algExpr.getCalledVariables
      (ae : algExpr)
      (callableVariables : List (varDecl))
      : Except String (List (String × List (varDecl))) := do
        match ae with
          | algExpr.number _ => return []
          | algExpr.cardExpression e => e.getCalledVariables callableVariables
          | algExpr.unaryAlgebraOperation _ ae =>
            ae.getCalledVariables callableVariables
          | algExpr.binaryAlgebraOperation _ ae1 ae2 =>
            let ae1_cv ← ae1.getCalledVariables callableVariables
            let ae2_cv ← ae2.getCalledVariables callableVariables
            return ae1_cv ++ ae2_cv
  end
end Shared
