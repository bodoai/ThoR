/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the data structures-/
import ThoR.Shared.Syntax.Mutuals.mutuals

import ThoR.Alloy.SymbolTable.VarDecl.varDecl

import Lean

open Lean
open Alloy

namespace Shared

  /-
  all replace calls
  -/
  mutual
    /--
    Replaces all calls to the callables from the List `callables`
    with their respective replacement
    in the given formula `f`
    -/
    partial def formula.replaceCalls
      (f: formula)
      (callables : List (varDecl))
      : formula := Id.run do
        match f with
          | formula.string _ =>

            /-
            there can be only calls the preds here.
            These currently do not need replacers
            -/
            return f

          | formula.pred_with_args n pas =>
            formula.pred_with_args
              n
              (pas.map fun pa =>
                pa.replaceCalls callables)

          | formula.unaryRelBoolOperation op e =>
            formula.unaryRelBoolOperation
              op
              (e.replaceCalls callables)

          | formula.unaryLogicOperation op f =>
            formula.unaryLogicOperation
              op
              (f.replaceCalls callables)

          | formula.binaryLogicOperation op f1 f2 =>
            formula.binaryLogicOperation
              op
              (f1.replaceCalls callables)
              (f2.replaceCalls callables)

          | formula.tertiaryLogicOperation op f1 f2 f3 =>
            formula.tertiaryLogicOperation
              op
              (f1.replaceCalls callables)
              (f2.replaceCalls callables)
              (f3.replaceCalls callables)

          | formula.algebraicComparisonOperation op ae1 ae2 =>
            formula.algebraicComparisonOperation op ae1 ae2

          | formula.relationComarisonOperation op e1 e2 =>
            formula.relationComarisonOperation
              op
              (e1.replaceCalls callables)
              (e2.replaceCalls callables)

          | formula.quantification q d n te forms =>
            formula.quantification
              q
              d
              n
              (te.replaceCalls callables)
              (forms.map fun f => f.replaceCalls callables)

          | formula.letDeclaration name value body =>
            formula.letDeclaration
              name
              (value.replaceCalls callables)
              (body.map fun f => f.replaceCalls callables)

    /--
    Replaces all calls to the callables from the List `callables`
    with their respective replacement
    in the given expression `e`
    -/
    partial def expr.replaceCalls
      (e: expr)
      (callables : List (varDecl))
      : expr := Id.run do
        match e with
          | expr.string s =>

            -- Get the names of the callable elements
            let callableNames := callables.map fun c => c.name

            /-
            if the called name is contained in the callable elements

            note that this should alway be the case, since if it is not contianed
            the symbol table should throw an error
            -/
            if callableNames.contains s then

              -- Get the index of the callable (the lists are same since since it was mapped)
              let callableIndex := callableNames.indexOf s

              -- Get the callable element
              let calledElement := callables.get! callableIndex

              -- Return the expression with the fitting replacement name
              return expr.string
                (if calledElement.isRelation then
                  (calledElement.getRelationReplacementName)
                else
                  (calledElement.getSignatureReplacementName))

            return e

          | expr.callFromOpen sn =>
            let ns := sn.representedNamespace.getId.toString
            let nsSplit := ns.splitOn "."

            /-
            This should never be empty
            -/
            if nsSplit.isEmpty then return e

            /-
            the called name is the last element of this split
            e.g. m1.a -> a is the called name
            -/
            let calledName := nsSplit.getLast!

            /-
            a namespace means that there is more than just the called name
            this has to be the case, since singular names are matched on string
            -/
            let namespacePresent := nsSplit.length > 1
            if !namespacePresent then return e

            -- the complete namespace
            let sigNamespace :=
              ((nsSplit.take (nsSplit.length - 1)).drop 1).foldl
                (fun result current => s!"{result}_{current}")
                (nsSplit.get! 0)

            -- the namespace with the last element removed (assumend to be a sig name)
            let relNamespace :=
              ((nsSplit.take (nsSplit.length - 2)).drop 1).foldl
                (fun result current => s!"{result}_{current}")
                (nsSplit.get! 0)

            let possibleCalls := callables.filter
              fun c =>
                -- the name has to be the name called
                c.name = calledName &&

                (
                -- if its a relation
                ( c.isRelation &&
                -- the signature name hast to be correct
                ( c.relationOf == nsSplit.get! (nsSplit.length - 2) &&
                -- and the namespace hast to be correct
                  (c.openedFrom == relNamespace) ||
                -- or not given for this
                  (c.openedFrom == "this" && relNamespace == "")))

                ||

                -- if its a signature
                ( !c.isRelation &&
                -- the namespace hast to be correct
                ( c.openedFrom == sigNamespace) ||
                -- or not given for this
                (c.openedFrom == "this" && relNamespace == ""))

                )

            -- Only one call should be possible (since the symbold table already checked)
            if !possibleCalls.length == 1 then return e

            let calledElement := possibleCalls.get! 0

            let identifer := mkIdent
              (if calledElement.isRelation then
                calledElement.getFullRelationName
              else
                calledElement.getFullSignatureName)

            return expr.callFromOpen (Alloy.separatedNamespace.mk identifer)

          | expr.binaryRelOperation op e1 e2 =>
            expr.binaryRelOperation
              op
              (e1.replaceCalls callables)
              (e2.replaceCalls callables)

          | expr.unaryRelOperation op e =>
            expr.unaryRelOperation
              op
              (e.replaceCalls callables)

          | expr.dotjoin dj e1 e2 =>
            expr.dotjoin
              dj
              (e1.replaceCalls callables)
              (e2.replaceCalls callables)

          | expr.string_rb _ => e
          | expr.const _ => e
          | expr.function_call_with_args functionName args =>
            expr.function_call_with_args
              functionName
              (args.map fun a => a.replaceCalls callables)
          | expr.ifElse condition thenBody elseBody =>
            expr.ifElse condition thenBody elseBody

    /--
    Replaces all calls to the callables from the List `callables`
    with their respective replacement
    in the given typeExpr `te`
    -/
    partial def typeExpr.replaceCalls
      (te: typeExpr)
      (callables : List (varDecl))
      : typeExpr := Id.run do
        match te with
          | typeExpr.arrowExpr ae =>
            typeExpr.arrowExpr
              (ae.replaceCalls callables)
          | typeExpr.multExpr m e =>
            typeExpr.multExpr
              m
              (e.replaceCalls callables)
          | typeExpr.relExpr e =>
            typeExpr.relExpr
              (e.replaceCalls callables)

    /--
  Replaces all calls to the callables from the List `callables`
  with their respective replacement
  in the given arrowOp `ao`
  -/
  partial def arrowOp.replaceCalls
    (ao: arrowOp)
    (callables :List (varDecl))
    : arrowOp :=
      match ao with
        | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
          arrowOp.multArrowOpExpr
            (e1.replaceCalls callables)
            m1
            m2
            (e2.replaceCalls callables)

        | arrowOp.multArrowOpExprLeft e m1 m2 ao1 =>
          arrowOp.multArrowOpExprLeft
            (e.replaceCalls callables)
            m1
            m2
            (ao1.replaceCalls callables)

        | arrowOp.multArrowOpExprRight ao1 m1 m2 e =>
          arrowOp.multArrowOpExprRight
            (ao1.replaceCalls callables)
            m1
            m2
            (e.replaceCalls callables)

        | arrowOp.multArrowOp ao1 m1 m2 ao2 =>
          arrowOp.multArrowOp
            (ao1.replaceCalls callables)
            m1
            m2
            (ao2.replaceCalls callables)

  end

end Shared
