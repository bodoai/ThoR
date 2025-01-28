/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.SymbolTable.varDecl
import ThoR.Alloy.Config

open Alloy Config
open Lean

namespace Shared.expr

  /--
  Replaces all calls to the callables from the List `callables`
  with their respective replacement
  in the given expression `e`
  -/
  def replaceCalls
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
          let ns := sn.representedNamespace.getId.lastComponentAsString
          let nsSplit := ns.splitOn "."

          /-
          This should never be empty
          -/
          if !nsSplit.isEmpty then

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

            if namespacePresent then

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
              if possibleCalls.length == 1 then
                let calledElement := possibleCalls.get! 0

                let identifer := mkIdent
                  (if calledElement.isRelation then
                    calledElement.getFullRelationName.toName
                  else
                    calledElement.getFullSignatureName.toName)

                return expr.callFromOpen (Alloy.separatedNamespace.mk identifer)

          return e

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

        | _ => e

  /--
  changes an expr (and all of its subexprs)
  to a string rb expression (if they are string)
  -/
  def toStringRb (e : expr) : expr :=
    match e with
      | expr.string s => expr.string_rb s
      | expr.binaryRelOperation op e1 e2 =>
        expr.binaryRelOperation op (e1.toStringRb) (e2.toStringRb)
      | expr.unaryRelOperation op e =>
        expr.unaryRelOperation op (e.toStringRb)
      | expr.dotjoin dj e1 e2 =>
        expr.dotjoin dj (e1.toStringRb) (e2.toStringRb)
      | e => e

  /--
  Generates a syntax representation of the type
  -/
  def toSyntax
    (blockName : Name)
    (e : expr)
    : TSyntax `expr := Unhygienic.run do
      match e with
        | expr.const c => `(expr| $(c.toSyntax):constant)
        | expr.string s => `(expr| $(mkIdent s.toName):ident)
        | expr.callFromOpen sn => `(expr| $(sn.toSyntax):separatedNamespace)
        | expr.unaryRelOperation op e => `(expr| $(op.toSyntax):unRelOp $(e.toSyntax blockName):expr)
        | expr.binaryRelOperation op e1 e2 =>
          `(expr| $(e1.toSyntax blockName):expr $(op.toSyntax):binRelOp $(e2.toSyntax blockName):expr)
        | expr.dotjoin dj e1 e2 =>
          `(expr|$(e1.toSyntax blockName):expr $(dj.toSyntax):dotjoin $(e2.toSyntax blockName):expr)
        -- FIXME In der folgenden Zeile fehlt noch das $rb -> Macht das Probleme?
        | expr.string_rb s => `(expr| @$(mkIdent s!"{blockName}.vars.{s}".toName):ident)

  /--
  Generates a Lean term corosponding with the type
  -/
  private def toTerm
    (e : expr)
    (inBLock : Bool)
    (blockName : Name)
    (quantorNames : List (String) := []) -- used to know which names must be pure
    : TSyntax `term := Unhygienic.run do
      match e with
        | expr.const c => return (c.toTerm)

        | expr.string s => do
          if inBLock && !(quantorNames.contains s) then
            `((
              ∻ $(mkIdent s!"{blockName}.vars.{s}".toName)
            ))
          else
            `($(mkIdent s.toName))

        | expr.callFromOpen sn =>
          let snt := sn.representedNamespace.getId.toString
          if inBLock then
            `((
              ∻ $(mkIdent s!"{blockName}.vars.{snt}".toName)
            ))
          else
            return sn.toTerm

        | expr.unaryRelOperation op e =>
          `(( $(op.toTerm)
              $(e.toTerm inBLock
                blockName quantorNames)
            ))

        | expr.binaryRelOperation op e1 e2 =>
          `(( $(op.toTerm)
              $(e1.toTerm inBLock
                blockName quantorNames
                )
              $(e2.toTerm inBLock
                blockName quantorNames
                )
            ))

        | expr.dotjoin dj e1 e2 =>
          `(( $(dj.toTerm)
              $(e1.toTerm inBLock
                blockName quantorNames
                )
              $(e2.toTerm inBLock
                blockName quantorNames
                )
            ))

        | expr.string_rb s => do
          `((@$(mkIdent s.toName) $(baseType.ident) _ _))

  /--
  Generates a Lean term corosponding with the type from outside an alloy block
  -/
  def toTermOutsideBlock
    (e : expr)
    (quantorNames : List (String) := [])
    :=
      toTerm e false `none quantorNames

  /--
  Generates a Lean term corosponding with the type from inside an alloy block
  -/
  def toTermFromBlock
    (e : expr)
    (blockName : Name)
    (quantorNames : List (String) := []) :=
      toTerm e true blockName quantorNames

  /--
  Parses the given syntax to the type
  -/
  partial def toType
    (e : TSyntax `expr)
    (signatureRelationNames : List String := [])
    : expr :=
      match e with
        | `(expr | ( $e:expr )) => expr.toType e
        | `(expr |
            $op:unRelOp
            $subExpr: expr) =>
            expr.unaryRelOperation
            (unRelOp.toType op)
            (expr.toType subExpr)

        | `(expr |
            $subExpr1:expr
            $op:binRelOp
            $subExpr2:expr) =>
            expr.binaryRelOperation
            (binRelOp.toType op)
            (expr.toType subExpr1)
            (expr.toType subExpr2)

        | `(expr |
            $subExpr1:expr
            $dj:dotjoin
            $subExpr2:expr) =>
            expr.dotjoin
            (dotjoin.toType dj)
            (expr.toType subExpr1)
            (expr.toType subExpr2)

        | `(expr | $const:constant) =>
            expr.const (constant.toType const)

        | `(expr | @$name:ident) => Id.run do
            expr.string_rb name.getId.toString

        | `(expr | $sn:separatedNamespace) =>
          expr.callFromOpen (Alloy.separatedNamespace.toType sn)

        | `(expr | $name:ident) => Id.run do
            let parsedName := name.getId

            if parsedName.isAtomic then

              let exprStringName := name.getId.lastComponentAsString

              -- If the string (name) of the expr is a sigField in a sigFact
              if (signatureRelationNames.contains exprStringName) then
                expr.dotjoin
                  dotjoin.dot_join
                  (expr.string "this")
                  (expr.string exprStringName)

              else
                expr.string exprStringName

            else -- ident contains . which must be parsed as dotjoin
              let x := (parsedName.splitAt (parsedName.components.length - 1))
              let subExpr1 := x.1
              let subExpr2 := x.2

              let subE1 : TSyntax `expr := Unhygienic.run
                `(expr| $(mkIdent subExpr1): ident)

              let subE2 : TSyntax `expr := Unhygienic.run
                `(expr| $(mkIdent subExpr2): ident)

              expr.dotjoin
                dotjoin.dot_join
                (expr.toType subE1)
                (expr.toType subE2)

        | `(expr | -- Hack to allow dotjoin before ()
          $subExpr1:expr .( $subExpr2:expr )) =>
          expr.dotjoin
            dotjoin.dot_join
            (expr.toType subExpr1)
            (expr.toType subExpr2)


        | _ => expr.const constant.none -- unreachable

  /--
  Gets the required variables for the type
  -/
  def getReqVariables
    (e : expr)
    : List (String) :=
      match e with
        | expr.string s => [s]
        | expr.callFromOpen sn => Id.run do
          -- this String can be something like m1.A
          let sns := sn.representedNamespace.getId.lastComponentAsString
          let snsSplit := sns.splitOn "."
          if snsSplit.isEmpty then
            return [sns]
          else
            [snsSplit.getLast!]
        | expr.unaryRelOperation _ e => e.getReqVariables
        | expr.binaryRelOperation _ e1 e2 => (e1.getReqVariables) ++ (e2.getReqVariables)
        | expr.dotjoin _ e1 e2 => (e1.getReqVariables) ++ (e2.getReqVariables)
        | _ => []

  def getStringExpr (e:expr) : String :=
    match e with
      | expr.string s => s
      | _ => default

  /--
  returns all signatures that are called and also are in the
  given name list (signature names).

  note that giving the names is required, since you can't decide
  on syntax alone if something is a signature or a relation
  -/
  def getSignatureCalls
    (e : expr)
    (signatureNames : List (String))
    (moduleName : String := default)
    : List (String) := Id.run do
      match e with
        | expr.string s =>
          if signatureNames.contains s then [s] else []

        | expr.callFromOpen sn =>
          let sns := sn.representedNamespace.getId.lastComponentAsString
          let snsSplit := sns.splitOn "."
          if snsSplit.isEmpty then
            if signatureNames.contains sns then [sns] else []
          else
            if signatureNames.contains snsSplit.getLast! then
              if (moduleName != default) && (snsSplit.get! 0) == "this" then
                [s!"{moduleName}.{snsSplit.getLast!}"]
              else
                [sns]
            else
              []

        | expr.unaryRelOperation _ e =>
          e.getSignatureCalls signatureNames

        | expr.binaryRelOperation _ e1 e2 =>
          (e1.getSignatureCalls signatureNames) ++
            (e2.getSignatureCalls signatureNames)

        | expr.dotjoin _ e1 e2 =>
          (e1.getSignatureCalls signatureNames) ++
            (e2.getSignatureCalls signatureNames)

        | _ => [] -- unreachable

  /--
  Gets all calls to the `callableVariables` which includes signatures and relations

  The result is a list of all called variables
  -/
  def getCalledVariables
    (e : expr)
    (callableVariables : List (varDecl))
    : (List (varDecl)) :=
      let callableVariableNames := (callableVariables.map fun cv => cv.name)

      match e with
      | expr.string s =>
        let isCallable := callableVariableNames.contains s
        if isCallable then
          let index := callableVariableNames.indexOf s
          let calledVariable := callableVariables.get! index
          [calledVariable]
        else
          []

      | expr.callFromOpen sn =>
        /-
        note that lastComponentAsString gets the full name as String since
        the name is enclosed in << >>
        -/
        let fullName := sn.representedNamespace.getId.lastComponentAsString
        let components := fullName.splitOn "."

        let calledVariableName := components.getLast!

        let possibleCalledVariables :=
          callableVariables.filter
            fun cv =>
              cv.name == calledVariableName

        if possibleCalledVariables.length == 1 then
          possibleCalledVariables
        else
          -- namespace if the called Variable is a signature
          let sigNamespace :=
            ((components.take (components.length - 1)).drop 1).foldl
              (fun result current => s!"{result}_{current}")
              (components.get! 0)

          -- the signature name if it is a relation
          let possibleSignatureName := components.get! (components.length - 2)
          -- the namespace with the last element removed (assumend to be a sig name)
          let relNamespace :=
            ((components.take (components.length - 2)).drop 1).foldl
              (fun result current => s!"{result}_{current}")
              (components.get! 0)

          possibleCalledVariables.filter
            fun pcv =>
              -- is either relation with correct sig name and namespace
              (
                pcv.isRelation &&
                pcv.relationOf == possibleSignatureName &&
                (if pcv.isOpened then pcv.openedFrom == relNamespace else true)
              ) ||
              -- or signature with correct namespace
              (
                !pcv.isRelation &&
                (if pcv.isOpened then pcv.openedFrom == sigNamespace else true)
              )

      | expr.unaryRelOperation _ e =>
        e.getCalledVariables callableVariables

      | expr.binaryRelOperation _ e1 e2 =>
        (e1.getCalledVariables callableVariables) ++
          (e2.getCalledVariables callableVariables)

      | expr.dotjoin _ e1 e2 =>
        (e1.getCalledVariables callableVariables) ++
          (e2.getCalledVariables callableVariables)

      | _ => []

  def getRelationCalls
    (e : expr)
    (relationNames : List (String))
    : List (String) := Id.run do
      match e with
        | expr.string s =>
          if relationNames.contains s then
            return [s]
          else
            return []

        | expr.callFromOpen sn =>
          let sns := sn.representedNamespace.getId.lastComponentAsString
          let snsSplit := sns.splitOn "."
          if snsSplit.isEmpty then
            if relationNames.contains sns then [sns] else []
          else
            if relationNames.contains snsSplit.getLast! then [sns] else []

        | expr.unaryRelOperation _ e =>
          e.getRelationCalls relationNames

        | expr.binaryRelOperation _ e1 e2 =>
          (e1.getRelationCalls relationNames) ++
            (e2.getRelationCalls relationNames)

        | expr.dotjoin _ e1 e2 =>
          let e1eval := (e1.getRelationCalls relationNames)
          let e2eval := (e2.getRelationCalls relationNames)
          if (e1eval.length == 0) && (e2eval.length == 1) then
            match e1 with
              | expr.string s =>
                let e2value := e2eval.get! 0
                return [s!"{s}.{e2value}"]

              | _ => return e1eval ++ e2eval

          else
            return e1eval ++ e2eval

        | _ => []

end Shared.expr
