/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Relation.Expr.expr
/-
import ThoR.Alloy.SymbolTable.VarDecl.varDecl
import ThoR.Alloy.SymbolTable.SymbolTable
import ThoR.Alloy.Config
import ThoR.Alloy.Syntax.AlloyData.alloyData
import ThoR.Alloy.UnhygienicUnfolder
import ThoR.Relation.ElabCallMacro
-/
import ThoR.Shared.Syntax.Mutuals.mutualsService

open Alloy Config
open Lean

namespace Shared.expr

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
      | expr.ifElse condition thenBody elseBody =>
        expr.ifElse condition (thenBody.toStringRb) (elseBody.toStringRb)
      | _ => e

  /--
  Generates a Lean term corosponding with the type
  -/
  private partial def toTerm
    (e : expr)
    (inBlock : Bool)
    (blockName : Name)
    (quantorNames : List (String) := []) -- used to know which names must be pure
    (availableAlloyData : List (alloyData) := [])
    (localContextUserNames : List Name := [])
    : Except String Term := do
      match e with
        | expr.const c =>
          return (c.toTerm)

        | expr.string s => do

          /-
          check if the name is defined in the existing modules, but only
          if the name is not defined in a variable definition
          -/
          if !inBlock && !(localContextUserNames.contains s.toName) then
            let mut possibleVarDecls := []
            for alloyData in availableAlloyData do
              let possibleMatches := alloyData.st.variableDecls.filter fun vd => vd.name == s
              if !possibleMatches.isEmpty then
                possibleVarDecls := possibleVarDecls.concat
                  (alloyData.st.name, possibleMatches)

            if !possibleVarDecls.isEmpty then
              if
                -- if there are matches in more than one module
                possibleVarDecls.length > 1 ||
                -- or more than one match in a module (this should be impossible)
                possibleVarDecls.any fun pv => pv.2.length > 1
              then
                throw s!"The call to {s} is ambiguous. \
                There are multiple declared variables which it could refer to ({possibleVarDecls})"

              let calledVarDecl := possibleVarDecls.get! 0
              let calledBlockName := calledVarDecl.1
              let callNameComponents := [calledBlockName, `vars, s.toName]
              let callName := Name.fromComponents callNameComponents
              return unhygienicUnfolder `((@$(mkIdent callName) $(baseType.ident) _ _))

          if inBlock && !(quantorNames.contains s) then
            return unhygienicUnfolder `((
              ∻ $(mkIdent s!"{blockName}.vars.{s}".toName)
            ))

          return unhygienicUnfolder `($(mkIdent s.toName))

        | expr.callFromOpen sn =>
          let snt := sn.representedNamespace.getId.toString
          if inBlock then
            return unhygienicUnfolder `((
              ∻ $(mkIdent s!"{blockName}.vars.{snt}".toName)
            ))
          else
            return sn.toTerm

        | expr.function_call_with_args called_function arguments =>
          let mut argumentsTerm :=
           unhygienicUnfolder
            `(($(← (arguments.get! 0).toTerm inBlock blockName quantorNames)))

          for arg in arguments.drop 1 do
            argumentsTerm :=
              unhygienicUnfolder
                `(argumentsTerm $(← arg.toTerm inBlock blockName quantorNames))

          let function_name_components := if inBlock then [blockName, `funs] else []
          let basic_function_name := called_function.toName
          let function_name := Name.fromComponents (function_name_components.concat basic_function_name)

          return unhygienicUnfolder `((
            ∻ $(mkIdent function_name)
          ) $argumentsTerm )

        | expr.unaryRelOperation op e =>
          let eTerm ← e.toTerm inBlock
            blockName quantorNames availableAlloyData localContextUserNames

          return unhygienicUnfolder `(( $(op.toTerm)
              $(eTerm)
            ))

        | expr.binaryRelOperation op e1 e2 =>
          let e1Term ← e1.toTerm inBlock
            blockName quantorNames availableAlloyData localContextUserNames
          let e2Term ← e2.toTerm inBlock
            blockName quantorNames availableAlloyData localContextUserNames
          return unhygienicUnfolder `(( $(op.toTerm)
              $(e1Term)
              $(e2Term)
            ))

        | expr.dotjoin dj e1 e2 =>
          let e1Term ← e1.toTerm inBlock
            blockName quantorNames availableAlloyData localContextUserNames
          let e2Term ← e2.toTerm inBlock
            blockName quantorNames availableAlloyData localContextUserNames
          return unhygienicUnfolder `(( $(dj.toTerm)
              $(e1Term)
              $(e2Term)
            ))

        | expr.string_rb s => do
          return unhygienicUnfolder
            `((@$(mkIdent s.toName) $(baseType.ident) _ _))

  /--
  Generates a Lean term corosponding with the type from outside an alloy block
  -/
  def toTermOutsideBlock
    (e : expr)
    (quantorNames : List (String) := [])
    (availableAlloyData : List (alloyData) := [])
    (localContextUserNames : List Name := [])
    :=
      toTerm e false `none quantorNames availableAlloyData localContextUserNames

  /--
  Generates a Lean term corosponding with the type from inside an alloy block
  -/
  def toTermFromBlock
    (e : expr)
    (blockName : Name)
    (quantorNames : List (String) := []) :=
      toTerm e true blockName quantorNames

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
  Parses the given syntax to the type
  -/
  partial def toType
    (e : Expression)
    (signatureRelationNames : List String := [])
    : Except String expr := do
      match e with
        | `(expr | ( $e:expr )) =>
          return ← expr.toType e
        | `(expr |
            $op:unRelOp
            $subExpr: expr) =>
            return expr.unaryRelOperation
              (← unRelOp.toType op)
              (← expr.toType subExpr)

        | `(expr |
            $subExpr1:expr
            $op:binRelOp
            $subExpr2:expr) =>
            return expr.binaryRelOperation
              (← binRelOp.toType op)
              (← expr.toType subExpr1)
              (← expr.toType subExpr2)

        | `(expr |
            $subExpr1:expr
            $dj:dotjoin
            $subExpr2:expr) =>
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
            [ $arguments:expr,* ]
          ) =>
          let mut arguments_typed := []
          for argument in arguments.getElems do
            arguments_typed := arguments_typed.concat (← expr.toType argument)

          return expr.function_call_with_args
            called_function.getId.toString
            arguments_typed

        | `(expr | -- Hack to allow dotjoin before ()
          $subExpr1:expr .( $subExpr2:expr )) =>
          return expr.dotjoin
            dotjoin.dot_join
            (← expr.toType subExpr1)
            (← expr.toType subExpr2)

        | `(expr |
          $subExpr1:expr .( $subExpr2:expr ). $subExpr3:expr) =>
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

  /--
  Gets all calls to the `callableVariables` which includes signatures and
  relations

  The result is a list of the call (in string from) and a (possibly empty) list
  of the concrete possible called variables (in form of varDecls). If the inner
  list contains more than one varDecl, called variable is ambiguous and could
  be either.
  -/
  def getCalledVariables
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

      | _ => return []

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
