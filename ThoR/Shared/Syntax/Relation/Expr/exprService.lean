/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Relation.Expr.expr
import ThoR.Alloy.SymbolTable.VarDecl.varDecl
import ThoR.Alloy.SymbolTable.SymbolTable
import ThoR.Alloy.Config
import ThoR.Alloy.Syntax.AlloyData.alloyData
import ThoR.Alloy.UnhygienicUnfolder
import ThoR.Relation.ElabCallMacro
import ThoR.Shared.Syntax.Mutuals.mutualsService

open Alloy Config
open Lean

namespace Shared.expr

  def isCallFromOpen (e : expr) : Bool :=
    match e with
      | expr.callFromOpen _ => true
      | _ => false

  def getCalledFromOpenData (e : expr) : separatedNamespace :=
    match e with
      | expr.callFromOpen data => data
      | _ => panic! s!"Tried to get callFromOpenData from expr {e}"

  def isString (e : expr) : Bool :=
    match e with
      | expr.string _ => true
      | _ => false

  def getStringData (e : expr) : String :=
    match e with
      | expr.string data => data
      | _ => panic! s!"Tried to get String data from expr {e}"

  /--
  If possible replace domain restrictions with relations.

  This is only possible, if the relation is restricted from the
  signature it is defined in.

  E.g. m1/a<:r gets simplified to the relation r IF r is a relation of a
  -/
  def simplifyDomainRestrictions
    (e : expr)
    (st : SymbolTable)
    : expr := Id.run do
    match e with
      | expr.binaryRelOperation operator leftSide rightSide =>
        -- needs to be domain restriction
        if !operator.isDomainRestriction then return e

        -- the right side needs to be a string for simplification
        if !rightSide.isString then return e

        let rightSideData := rightSide.getStringData
        let possibleRelations :=
          st.variableDecls.filter
            fun vd => vd.isRelation && vd.name == rightSideData

        /-
        if left and right sides are strings then it could be a call
        to a LOCAL relation
        -/
        if leftSide.isString then
          let leftSideData := leftSide.getStringData
          let matchingRelations :=
            possibleRelations.filter
              fun pr =>
                pr.relationOf == leftSideData &&
                !pr.isOpened

          -- if there is one matching relation use it
          if
            !matchingRelations.isEmpty &&
            !matchingRelations.length > 1
          then
            let components := [`this, leftSideData.toName, rightSideData.toName]
            let ident := mkIdent (Name.fromComponents components)
            return expr.callFromOpen (Alloy.separatedNamespace.mk ident)

        /-
        if the left side is a call to another module, then it has to
        be a relation from this module
        -/
        if !leftSide.isCallFromOpen then return e

        let leftSideData := leftSide.getCalledFromOpenData

        let leftSideComponents :=
          leftSideData.representedNamespace.getId.components

        if leftSideComponents.isEmpty then return e

        let moduleNameComponents :=
          leftSideComponents.take (leftSideComponents.length - 1)
        let moduleName :=
          (moduleNameComponents.drop 1).foldl
          (fun result component => s!"{result}_{component.toString}")
          (moduleNameComponents.get! 0).toString

        let signatureName := leftSideComponents.getLast!

        let matchingRelations :=
          possibleRelations.filter
            fun pr =>
              pr.relationOf == signatureName.toString &&
              pr.isOpened &&
              pr.openedFrom == moduleName

        -- if matching relations are not exactly one return e
        if
          matchingRelations.isEmpty ||
          matchingRelations.length > 1
        then
          return e

        let components := leftSideComponents.concat rightSideData.toName
        let ident := mkIdent (Name.fromComponents components)
        return expr.callFromOpen (Alloy.separatedNamespace.mk ident)

      | _ => e

  /--
  Transforms an expr_without_if to an expr via the
  shortcut of adding parenthesis
  -/
  private def expr_without_if_to_expr
    (e : Expression_without_if)
    : Expression := Unhygienic.run do
      return ← `(expr | ( $e:expr_without_if ))

  /--
  Parses the given syntax to the type
  -/
  partial def toType
    (e : Expression)
    (signatureRelationNames : List String := [])
    : Except String expr := do
      match e with
        | `(expr | ( $e:expr )) =>
          return ← expr.toType e

        | `(expr | ( $e:expr_without_if )) =>
          return ← expr.toType (expr_without_if_to_expr e)

        | `(expr |
            $op:unRelOp
            $subExpr: expr_without_if) =>
            return expr.unaryRelOperation
              (← unRelOp.toType op)
              (← expr.toType subExpr)

        | `(expr |
            $subExpr1:expr_without_if
            $op:binRelOp
            $subExpr2:expr_without_if) =>
            return expr.binaryRelOperation
              (← binRelOp.toType op)
              (← expr.toType subExpr1)
              (← expr.toType subExpr2)

        | `(expr |
            $subExpr1:expr_without_if
            $dj:dotjoin
            $subExpr2:expr_without_if) =>
            return expr.dotjoin
              (← dotjoin.toType dj)
              (← expr.toType subExpr1)
              (← expr.toType subExpr2)

        | `(expr | $const:constant) =>
            return expr.const (← constant.toType const)

        | `(expr | @$name:ident) =>
            return expr.string_rb name.getId.toString

        | `(expr | $sn:separatedNamespace) =>
          let sn ← Alloy.separatedNamespace.toType sn
          let components := sn.representedNamespace.getId.components
          let lastComponent := components.getLast!
          let lastComponentString := lastComponent.toString

          let split := lastComponentString.splitOn "<:"
          let splitNames := split.map fun c => c.toName
          let newComponents := (components.take (components.length - 1)) ++ splitNames
          let newName := Name.fromComponents newComponents
          let newIdent := mkIdent newName
          return expr.callFromOpen (Alloy.separatedNamespace.mk newIdent)

        | `(expr | $name:ident) =>
            let parsedName := name.getId

            if parsedName.isAtomic then

              let exprStringName := name.getId.toString

              -- If the string (name) of the expr is a sigField in a sigFact
              if (signatureRelationNames.contains exprStringName) then
                return expr.dotjoin
                  dotjoin.dot_join
                  (expr.string "this")
                  (expr.string exprStringName)

              else
                return expr.string exprStringName

            else -- ident contains . which must be parsed as dotjoin
              let x := (parsedName.splitAt (parsedName.components.length - 1))
              let subExpr1 := x.1
              let subExpr2 := x.2

              let subE1 : Expression := Unhygienic.run
                `(expr| $(mkIdent subExpr1): ident)

              let subE2 : Expression := Unhygienic.run
                `(expr| $(mkIdent subExpr2): ident)

              return expr.dotjoin
                dotjoin.dot_join
                (← expr.toType subE1)
                (← expr.toType subE2)

        | `(expr |
            $called_function:ident
            [ $arguments:expr_without_if,* ]
          ) =>
          let mut arguments_typed := []
          for argument in arguments.getElems do
            arguments_typed := arguments_typed.concat (← expr.toType argument)

          return expr.function_call_with_args
            called_function.getId.toString
            arguments_typed

        | `(expr | -- Hack to allow dotjoin before ()
          $subExpr1:expr_without_if .( $subExpr2:expr_without_if )) =>
          return expr.dotjoin
            dotjoin.dot_join
            (← expr.toType subExpr1)
            (← expr.toType subExpr2)

        | `(expr |
          $subExpr1:expr_without_if .( $subExpr2:expr_without_if ). $subExpr3:expr_without_if) =>
          return expr.dotjoin
            dotjoin.dot_join
            (← expr.toType subExpr1)
            (expr.dotjoin
              dotjoin.dot_join
              (← expr.toType subExpr2)
              (← expr.toType subExpr3))

        | syntx =>
            throw s!"No match implemented in \
            exprService.toType \
            for '{syntx}'"

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
          let sns := sn.representedNamespace.getId.toString
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

  def insertModuleVariables
    (e : expr)
    (moduleVariables openVariables : List (String))
    : expr := Id.run do
      match e with
        | expr.string s =>
          if !moduleVariables.contains s then return e

          let index := moduleVariables.indexOf s
          let replacer := openVariables.get! index
          return expr.string replacer

        | expr.unaryRelOperation op e =>
          expr.unaryRelOperation
            op
            (e.insertModuleVariables moduleVariables openVariables)
        | expr.binaryRelOperation op e1 e2 =>
          expr.binaryRelOperation
            op
            (e1.insertModuleVariables moduleVariables openVariables)
            (e2.insertModuleVariables moduleVariables openVariables)
        | expr.dotjoin dj e1 e2 =>
          expr.dotjoin
            dj
            (e1.insertModuleVariables moduleVariables openVariables)
            (e2.insertModuleVariables moduleVariables openVariables)

        | _ => e

  /--
  replaces calls to "this" (current module), with a call to the given module
  name.
  -/
  def replaceThisCalls
    (e : expr)
    (moduleName : String)
    : expr := Id.run do
      match e with

        | expr.callFromOpen sn =>
          let components := sn.representedNamespace.getId.components
          if !components.get! 0 == `this then return e
          let moduleName := (moduleName.splitOn "_").getLast!
          let new_components := [moduleName.toName] ++ (components.drop 1)
          let new_ident := mkIdent (Name.fromComponents new_components)

          expr.callFromOpen
            (separatedNamespace.mk new_ident)

        | expr.unaryRelOperation op e =>
          expr.unaryRelOperation
            op
            (e.replaceThisCalls moduleName)
        | expr.binaryRelOperation op e1 e2 =>
          expr.binaryRelOperation
            op
            (e1.replaceThisCalls moduleName)
            (e2.replaceThisCalls moduleName)
        | expr.dotjoin dj e1 e2 =>
          expr.dotjoin
            dj
            (e1.replaceThisCalls moduleName)
            (e2.replaceThisCalls moduleName)

        | _ => e

  def getFunctionCalls
    (e : expr)
    (callableFunctions : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String
      (List (commandDecl × List (expr × List (String × List (varDecl))))) := do
    match e with
      | expr.string s =>
        let possibleFunctions := callableFunctions.filter fun cf => cf.name == s
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

      | expr.callFromOpen _ => return [] -- possibly incorrect
      | expr.string_rb _ => return []
      | expr.const _ => return []

end Shared.expr
