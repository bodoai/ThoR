/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/-
The purpose of this file is to create and evaluate (or elaborate) the alloy block command,
which serves as entrance point to the Alloy syntax in Lean.
-/
import ThoR.Relation

import ThoR.Shared.Syntax

import ThoR.Alloy.Config
import ThoR.Alloy.UnhygienicUnfolder

import ThoR.Alloy.Syntax.AST
import ThoR.Alloy.SymbolTable.SymbolTable
import ThoR.Alloy.SymbolTable.SymbolTableService
import ThoR.Alloy.InheritanceTree.UnTyped.InheritanceTree

import ThoR.Alloy.Syntax.Signature.SigDecl.sigDeclService

import ThoR.Alloy.Syntax.SeparatedNamespace
import ThoR.Alloy.Syntax.alloyData
import ThoR.Alloy.Syntax.OpenModule.openModuleHelper

import ThoR.Shared.Syntax.TypeExpr.typeExprService

open ThoR Shared Alloy Config
open Lean Lean.Elab Command Term

/--
Creates commands to create all variables from the given variable declarations and the block name.

The created vars are inside a namespace named blockname and inside a type class
named var.
-/
private def createVariableCommands
  (blockName : Name)
  (variableDecls : List (varDecl))
  : List Command := Unhygienic.run do
    let mut commandList : List Command := []

    if variableDecls.isEmpty then
      return commandList
    else

      let blockNameIdent := mkIdent blockName

      --NamespaceBegin
      commandList := commandList.concat (← `(namespace $blockNameIdent))

      --TypeClass
      let mut variableFields :
        Array (TSyntax ``Lean.Parser.Command.structExplicitBinder) := #[]

      for vd in variableDecls do
        let newName :=
          if vd.isRelation then
             vd.getRelationReplacementName.toName
          else
            vd.getSignatureReplacementName.toName

        let type :=
          (vd.type.replaceCalls variableDecls)

        let varField ←
          `(Lean.Parser.Command.structExplicitBinder |
              ($(mkIdent newName) : ∷ $(type.toSyntax blockNameIdent.getId)))

        variableFields := variableFields.push varField

      let id : Ident := mkIdent "vars".toName
      let mut variableTypeclass : Command ←
      `(class $id ($baseType.ident : Type) [$(mkIdent ``ThoR.TupleSet) $baseType.ident] where
          $[$variableFields]*
        )
      commandList := commandList.concat variableTypeclass

      --NamespaceEnd
      commandList := commandList.concat (← `(end $blockNameIdent))

      return commandList

/--
Creates a single creation command of either a definition or an axiom from a
given command declaration and the blockname.

What is created depends on the commandType of cd
-/
private def createDefOrAxiomCommand
  (blockName : Name)
  (cd : commandDecl)
  (callableVariables : List (varDecl))
  : Except String Command := do

    -- formula evaluation
    -- All formulas (lines) in an Alloy pred or in an Alloy fact are
    -- transformed into a conjunction of all these formulas.
    let emptyTerm : Term := unhygienicUnfolder `($(mkIdent "".toName))
    let mut bodyTerm : Term := emptyTerm

    -- if it is not a function it has formulas
    if !(cd.isFunction) && !(cd.formulas.isEmpty) then
      let forms :=
        (cd.formulas.map
          fun f =>
            f.replaceCalls callableVariables)

      let argnames := (cd.predArgs.map fun (arg) => arg.1.names).join

      let ff := (forms.get! 0)
      bodyTerm ←
        ff.toTerm
          blockName cd.requiredVars callableVariables cd.predCalls argnames

      for formula in forms.drop 1 do
        let newTerm ←
          formula.toTerm
            blockName cd.requiredVars callableVariables cd.predCalls argnames
        bodyTerm := unhygienicUnfolder `($bodyTerm ∧ ($newTerm))

    -- function only has expressions
    if cd.isFunction && !(cd.expressions.isEmpty) then
      let expressions :=
        cd.expressions.map fun e => e.replaceCalls callableVariables


      let fe := (expressions.get! 0)
      bodyTerm := fe.toTermFromBlock blockName

      for expression in expressions.drop 1 do
        let newTerm := expression.toTermFromBlock blockName
        bodyTerm := unhygienicUnfolder `($bodyTerm ∧ ($newTerm))

    -- and ifExpressions
    if cd.isFunction && !(cd.ifExpressions.isEmpty) then
      let ifExpressions :=
        cd.ifExpressions.map fun ie =>
          {ie with
            condition := ie.condition.replaceCalls callableVariables,
            thenBody := ie.thenBody.replaceCalls callableVariables,
            elseBody := ie.elseBody.replaceCalls callableVariables
          }

      for ifExpression in ifExpressions do
        let conditionTerm ←
          ifExpression.condition.toTerm blockName cd.requiredVars callableVariables cd.predCalls

        let thenTerm := ifExpression.thenBody.toTermFromBlock blockName
        let elseTerm :=
          if ifExpression.hasElse then
            ifExpression.thenBody.toTermFromBlock blockName
          else
            unhygienicUnfolder `(True)

        -- possibly wrong
        let newTerm := unhygienicUnfolder `(if ( $(conditionTerm) == True) then $(thenTerm) else $(elseTerm))

        bodyTerm := unhygienicUnfolder `($bodyTerm ∧ ($newTerm))

    -- define command
    let tupleSetArg
      : Array (TSyntax ``Lean.Parser.Term.bracketedBinderF) :=
    #[
      (unhygienicUnfolder `(Lean.Parser.Term.bracketedBinderF |
        {$(baseType.ident) : Type}
      )),
      (unhygienicUnfolder `(Lean.Parser.Term.bracketedBinderF |
        [$(mkIdent ``ThoR.TupleSet) $(baseType.ident)]
      )),
      (unhygienicUnfolder `(Lean.Parser.Term.bracketedBinderF |
        [$(mkIdent s!"{blockName}.vars".toName) $(baseType.ident)]
      ))
    ]

    -- facts only have default arguments command
    if cd.isFact then
      if bodyTerm != emptyTerm then
        return unhygienicUnfolder `(axiom $(mkIdent cd.name.toName) $[$tupleSetArg]* : $bodyTerm)
      else
        return unhygienicUnfolder `(
          axiom $(mkIdent cd.name.toName)
          $[$tupleSetArg]*
          : True )

    -- functions, asserts and predicates are similar
    if cd.isPredicate || cd.isFunction || cd.isAssert then
      let mut argTerms :
        TSyntax ``Lean.Parser.Command.optDeclSig :=
          unhygienicUnfolder `(Lean.Parser.Command.optDeclSig | $[$tupleSetArg]*)

      let mut allArgs : Array (TSyntax ``Lean.Parser.Term.bracketedBinderF) :=
        tupleSetArg

      -- predicate arguments
      if cd.isPredicate && !(cd.predArgs.isEmpty) then
        for arg in cd.predArgs do
          let argExpr := arg.1.expression.replaceCalls callableVariables
          let type := typeExpr.relExpr argExpr.toStringRb
          let typeSyntax := type.toSyntax blockName
          let names := (arg.1.names.map fun name => (mkIdent name.toName)).toArray
          let unhygienicTerm :=
            `(Lean.Parser.Term.bracketedBinderF | ($[$names]* : ∷ $typeSyntax))
          let term := unhygienicUnfolder unhygienicTerm
          allArgs := allArgs.push term
        argTerms := unhygienicUnfolder `(Lean.Parser.Command.optDeclSig| $[$allArgs]*)

      -- function arguments
      if cd.isFunction && !(cd.functionArgs.isEmpty) then
        for arg in cd.functionArgs do
          let type := (arg.1.type.replaceCalls callableVariables).toStringRb
          let typeSyntax := type.toSyntax blockName
          let names := (arg.1.names.map fun name => (mkIdent name.toName)).toArray
          let unhygienicTerm :=
            `(Lean.Parser.Term.bracketedBinderF | ($[$names]* : ∷ $typeSyntax))
          let term := unhygienicUnfolder unhygienicTerm
          allArgs := allArgs.push term

      -- add function arguments and function return type
      if cd.isFunction then
        let returnType :=
          (cd.functionReturnType.replaceCalls callableVariables).toStringRb
        let returnTypeSyntax := returnType.toSyntax blockName
        argTerms := unhygienicUnfolder
          `(Lean.Parser.Command.optDeclSig| $[$allArgs]* : ∷ $returnTypeSyntax)

        bodyTerm := unhygienicUnfolder `(cast ($(bodyTerm)) ∷ $returnTypeSyntax)

      if bodyTerm != emptyTerm then
        return unhygienicUnfolder `(
          def $(mkIdent cd.name.toName)
          $argTerms
          := $bodyTerm)
      else
        return unhygienicUnfolder `(
          def $(mkIdent cd.name.toName)
          $argTerms
          := True )

    throw s!"Can't create {cd}. Elaboration for {cd.commandType} is not implemented"

/--
Creates commands to create Lean definitions from the given blockname and commandDecls.

The created commands are encapsulated in a namespace with the given Name
-/
private def createDefsCommandsWithNamespace
  (blockName : Name)
  (namespaceName : Name)
  (commandDecls : List (commandDecl))
  (callableVariables : List (varDecl))
  : Except String (List Command) := do
    let mut commandList : List Command := []

    if commandDecls.isEmpty then
      return commandList
    else

      --NamespaceBegin
      commandList := commandList.concat
        (unhygienicUnfolder `(namespace $(mkIdent namespaceName)))

      --BaseTypeDecl
      let defsBaseType : Command :=
        unhygienicUnfolder
          `(variable {$baseType.ident : Type}
            [$(mkIdent ``ThoR.TupleSet) $baseType.ident]
            [$(mkIdent (s!"{blockName}.vars").toName) $baseType.ident])

      commandList := commandList.concat defsBaseType

      --Def declaration
      for cd in commandDecls do
        let cdCmd ← (createDefOrAxiomCommand blockName cd callableVariables)
        commandList := commandList.concat cdCmd

      --NamespaceEnd
      commandList := commandList.concat
        (unhygienicUnfolder `(end $(mkIdent namespaceName)))

      return commandList

/--
Creates commands to create Lean definitions (for preds) from the given
blockname and commandDecls.

The created commands are encapsulated in a namespace named blockname.preds
-/
private def createPredDefsCommands
  (blockName : Name)
  (defDecls : List (commandDecl))
  (callableVariables : List (varDecl))
  : Except String (List Command) :=
    createDefsCommandsWithNamespace
      (namespaceName := s!"{blockName}.preds".toName)
      blockName defDecls callableVariables

/--
Creates commands to create Lean definitions (for functions) from the given
blockname and commandDecls.

The created commands are encapsulated in a namespace named blockname.functions
-/
private def createFunctionDefsCommands
  (blockName : Name)
  (defDecls : List (commandDecl))
  (callableVariables : List (varDecl))
  : Except String (List ((TSyntax `command))) :=
    createDefsCommandsWithNamespace
      (namespaceName := s!"{blockName}.functions".toName)
      blockName defDecls callableVariables

/--
Creates commands to create Lean definitions (for asserts) from the given
blockname and commandDecls.

The created commands are encapsulated in a namespace named blockname.asserts
-/
private def createAssertDefsCommands
  (blockName : Name)
  (defDecls : List (commandDecl))
  (callableVariables : List (varDecl))
  : Except String (List Command) :=
    createDefsCommandsWithNamespace
      (namespaceName := s!"{blockName}.asserts".toName)
      blockName  defDecls callableVariables

/--
Creates commands to create Lean axioms from the given blockname and commandDecls.

The created commands are encapsulated in a namespace named blockname.facts
-/
private def createAxiomCommands
  (blockName : Name)
  (axiomDecls : List (commandDecl))
  (callableVariables : List (varDecl))
  : Except String (List Command) := do
    let mut commandList : List Command := []

    if axiomDecls.isEmpty then
      return commandList
    else

      let namespaceName := (s!"{blockName}.facts").toName

      --NamespaceBegin
      commandList := commandList.concat
        ( unhygienicUnfolder `(namespace $(mkIdent namespaceName)))

      --BaseTypeDecl
      let defsBaseType : Command :=
        unhygienicUnfolder
          `(variable {$(baseType.ident) : Type}
            [$(mkIdent ``ThoR.TupleSet) $(baseType.ident)]
            [$(mkIdent (s!"{blockName}.vars").toName) $(baseType.ident)])

      commandList := commandList.concat defsBaseType

      --Axiom declaration
      for ad in axiomDecls do
        let adCmd ← (createDefOrAxiomCommand blockName ad callableVariables)
        commandList := commandList.concat adCmd

      --NamespaceEnd
      commandList := commandList.concat
        (unhygienicUnfolder `(end $(mkIdent namespaceName)))

      return commandList

/--
Creates commands to create Lean aliases for variable declarations

These are intendet to offer a natural (alloy-like) way to acces these variables
-/
private def createVariableAliasCommands
  (blockName : Name)
  (variableDeclarations : List (varDecl))
  : List Command := Unhygienic.run do
    let mut commandList : List Command := []
    for variableDeclaration in variableDeclarations do

      /-
      The "undottet" name is the name created by the definition. It
      contains undesireable symbols like the relation separator.
      -/
      let mut undottetComponents :=
        blockName.components.concat "vars".toName

      /-
      Get the correct replacement name
      -/
      if variableDeclaration.isRelation then
        undottetComponents :=
          undottetComponents.concat
            variableDeclaration.getRelationReplacementName.toName
      else
        undottetComponents :=
          undottetComponents.concat
            variableDeclaration.getSignatureReplacementName.toName

      let undottetName := Name.fromComponents undottetComponents

      /-
      The "dottet" name has the undesired symbols replaced by dots.
      -/
      let mut dottetComponents :=
        blockName.components.concat "vars".toName

      /-
      the alloy "dottet" name provides alloy like module access.
      this works by creating another alias which contains only
      the last element of the module name.

      (this is only created if it differs from the regual dotted name)
      -/
      let mut alloyDottedComponents := dottetComponents

      if variableDeclaration.isOpened then
        let openedFromSplit := variableDeclaration.openedFrom.splitOn "_"
        for element in openedFromSplit do
          dottetComponents :=
            (dottetComponents.concat element.toName)

        alloyDottedComponents :=
          (alloyDottedComponents.concat openedFromSplit.getLast!.toName)

      let mut nameComponents := []
      if variableDeclaration.isRelation then
        nameComponents :=
          nameComponents.concat variableDeclaration.relationOf.toName
      nameComponents := nameComponents.concat variableDeclaration.name.toName

      dottetComponents :=
        dottetComponents.append
          nameComponents

      alloyDottedComponents :=
        alloyDottedComponents.append
          nameComponents

      let dottetName := Name.fromComponents dottetComponents
      let alloyDottetName := Name.fromComponents alloyDottedComponents

      let command ← `(alias $(mkIdent dottetName) := $(mkIdent undottetName))
      commandList := commandList.concat command

      if dottetName != alloyDottetName then
        let command ← `(alias $(mkIdent alloyDottetName) := $(mkIdent undottetName))
        commandList := commandList.concat command

    return commandList

/--
Creates commands to create all variables, definitions and axioms in Lean.

The created commands are encapsulated in a namespaces, which are opened as the last command.
-/
private def createCommands (st : SymbolTable)
  : Except String (List Command) := do

    let blockName : Name := st.name
    let mut namespacesToOpen : Array (Ident) := #[]

    --variables
    let mut commandList : List Command := []

    let varCommands := createVariableCommands blockName st.variableDecls
    commandList := commandList.append varCommands
    if !(varCommands.isEmpty) then
      namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.vars".toName)

    -- creating aliases
    let aliasCommands := createVariableAliasCommands blockName st.variableDecls
    commandList := commandList.append aliasCommands

    -- predicates
    let predCommands ← createPredDefsCommands blockName (st.defDecls.filter fun dd => dd.isPredicate) st.variableDecls
    commandList := commandList.append predCommands
    if !(predCommands.isEmpty) then
      namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.preds".toName)

    -- functions
    let functionCommands ← createFunctionDefsCommands blockName (st.defDecls.filter fun dd => dd.isFunction) st.variableDecls
    commandList := commandList.append functionCommands
    if !(functionCommands.isEmpty) then
      namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.functions".toName)

    -- axioms
    let axCommands ← createAxiomCommands blockName st.axiomDecls st.variableDecls
    commandList := commandList.append axCommands
    if !(axCommands.isEmpty) then
      namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.facts".toName)

    -- asserts
    let assertCommands ← createAssertDefsCommands blockName st.assertDecls st.variableDecls
    commandList := commandList.append assertCommands
    if !(assertCommands.isEmpty) then
      namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.asserts".toName)

    -- open the namespaces to use all withot explicit calling
    let openDecl : TSyntax ``Lean.Parser.Command.openDecl :=
      unhygienicUnfolder `(Lean.Parser.Command.openDecl|
        $[$(namespacesToOpen)]*
      )
    commandList := commandList.concat (unhygienicUnfolder `(open $openDecl))

    return commandList

declare_syntax_cat moduleVar
syntax ("exactly")? ident : moduleVar
abbrev ModuleVar := Lean.TSyntax `moduleVar

private def moduleVar.getIdent
  (mv : ModuleVar)
  : Ident :=
    match mv with
      | `(moduleVar | exactly $i:ident) => i
      | `(moduleVar | $i:ident) => i
      | _ => unreachable!

/--
Represents the syntax for the alloy block.

Options:
- To get a logoutput: #alloy
- To succeed on failure (with the exception of syntax errors): ~alloy
-/
syntax (name := alloyBlock)
  ("#" <|> "~")?
  "alloy"
  (("module")? separatedNamespace ("[" moduleVar,+ "]")?)?
  specification*
  "end"
  : command

/--
This function tries to recursivly open all modules.
-/
private partial def openModules
  (ast_withUnopenedModules : AST)
  (env : Environment)
  : Except String AST := do

    let mut ast_withOpenedModules := ast_withUnopenedModules.clearModulesToOpen

    -- for each opened Module, add all of their ASTS
    for moduleToOpen in ast_withUnopenedModules.modulesToOpen do
      match (openModule.toAlloyData moduleToOpen env) with
        | Except.error msg =>
          throw msg
        | Except.ok data =>
          let mut newAst := data.ast

          -- if an alias is defined, use it as name for the module
          if moduleToOpen.moduleAlias != default then
            newAst := newAst.updateName moduleToOpen.moduleAlias

          let variablesOnOpen := moduleToOpen.moduleVariables
          let numberOfVariablesOnOpen := variablesOnOpen.length

          let variablesOnModule := newAst.modulVariables
          let numberOfVariablesOnModule := variablesOnModule.length

          /-
          the open and the module need to have
          the same number of arguments
          -/
          if
            !(numberOfVariablesOnOpen ==
            numberOfVariablesOnModule)
          then
            throw s!"The module {newAst.name} was openend \
            with {numberOfVariablesOnOpen} arguments ({variablesOnOpen}) \
            , but the expected number of arguments is {numberOfVariablesOnModule}"

          /-
          if the module has Variables (and passed previous check)
          then the variables are to be replaced
          -/
          if !variablesOnOpen.isEmpty then

            newAst :=
              newAst.updateSigDecls
                (newAst.sigDecls.map
                  fun sd => sd.insertModuleVariables variablesOnModule variablesOnOpen)

            newAst :=
              newAst.updateFactDecls
                (newAst.factDecls.map
                  fun fd => fd.insertModuleVariables variablesOnModule variablesOnOpen)

            newAst :=
              newAst.updateAssertDecls
                (newAst.assertDecls.map
                  fun ad => ad.insertModuleVariables variablesOnModule variablesOnOpen)

            newAst :=
              newAst.updatePredDecls
                (newAst.predDecls.map
                  fun dd => dd.insertModuleVariables variablesOnModule variablesOnOpen)

          if !newAst.modulesToOpen.isEmpty then
            let additionalModules := (openModules newAst env)
            match additionalModules with
              | Except.error msg => throw msg
              | Except.ok newData =>
                newAst := newAst.addOpenedModule newData

          ast_withOpenedModules := ast_withOpenedModules.addOpenedModule newAst

    return ast_withOpenedModules

/--
Evaluates the alloy block syntax.
-/
private def evalAlloyBlock
  (name : Ident)
  (specifications : Array Specification)
  (moduleVariables : List (String) := default)
  (logging: Bool := false)
  : CommandElabM Unit := do

    let monadeState ← get
    let monadeEnv := monadeState.env

    let mut ast := AST.create name specifications moduleVariables
    if logging then
      logInfo
        s!"AST without opened Modules: \n
        {ast.toString}"

    let module_variables_with_number_of_occurences :=
      ( ast.modulVariables.map
        fun elem => (elem, ast.modulVariables.count elem)
      ).dedup

    for module_variable in module_variables_with_number_of_occurences do
      let module_variable_name := module_variable.1
      let module_variable_number_of_occurences := module_variable.2

      if module_variable_number_of_occurences > 1 then
        logError s!"The Module {ast.name} has \
        {module_variable_number_of_occurences} module variables \
        with the name {module_variable_name}. Module variable names \
        must be unique."

    -- try to open all modules
    let ast_withExcept := openModules ast monadeEnv

    -- if an exception occured: log it and abort
    match ast_withExcept with
      | Except.error msg =>
        logError msg
        return
      | Except.ok result_ast =>
        ast := result_ast

    if logging then
      logInfo
        s!"AST with opened Modules: \n
        {ast.toString}"

    let result := SymbolTable.create ast logging
    match result with
      | Except.error msg =>
        logError msg

      | Except.ok st =>

        if logging then logInfo st.toString

        let data : alloyData := {ast := ast, st := st}

        let newMonadeEnv := addAlloyData monadeEnv data

        match newMonadeEnv with
          | Except.ok nme =>
            setEnv nme
            if logging then
              logInfo s!"Storing the Data as environment \
              extension under the name {data.ast.name}_Data"

          | Except.error e => logError e

/--
Finds a suitable defaultName for unnamed Blocks.
-/
private partial def findDefaultName
  (env: Environment)
  (defaultName: Name := `default) -- defaultName here
  (depth : Int := 0)
  : Name := Id.run  do
    let mut finalDefaultName := defaultName

    let namespaceNames := Lean.namespacesExt.getEntries env

    --add Depth to Name
    if depth > 0 then
      finalDefaultName := s!"{defaultName}{depth}".toName

    let extensions := [
      "",
      ".vars",
      ".preds",
      ".facts",
      ".inheritance_facts"
    ]

    let finalDefaultNameToCheck : List Name :=
      List.foldl
        (fun lst suf => lst.concat (s!"{finalDefaultName}{suf}".toName))
        []
        extensions

    if finalDefaultNameToCheck.any (fun elem => namespaceNames.contains elem) then
      return findDefaultName env defaultName (depth+1)
    else
      return finalDefaultName

/--
Implementation for the alloy block syntax
-/
@[command_elab alloyBlock]
private def alloyBlockImpl : CommandElab := fun stx => do
  try
    match stx with
      | `(alloy $blockName:separatedNamespace
            $specifications:specification* end) =>

          let blockName :=
            (separatedNamespace.toType blockName).representedNamespace

          evalAlloyBlock blockName specifications

      | `(alloy $blockName:separatedNamespace [$mvs:moduleVar,*]
            $specifications:specification* end) =>

          let blockName :=
            (separatedNamespace.toType blockName).representedNamespace

          let moduleVariables :=
            (mvs.getElems.map
              fun mv =>
              (moduleVar.getIdent mv).getId.toString
            ).toList

          evalAlloyBlock
            (moduleVariables := moduleVariables)
            blockName
            specifications

      | `(alloy module $blockName:separatedNamespace
            $specifications:specification* end) =>

          let blockName :=
            (separatedNamespace.toType blockName).representedNamespace

          evalAlloyBlock blockName specifications

      | `(alloy module $blockName:separatedNamespace [$mvs:moduleVar,*]
            $specifications:specification* end) =>

          let blockName :=
            (separatedNamespace.toType blockName).representedNamespace

          let moduleVariables :=
            (mvs.getElems.map
              fun mv =>
              (moduleVar.getIdent mv).getId.toString
            ).toList

          evalAlloyBlock
            (moduleVariables := moduleVariables)
            blockName
            specifications

      | `(alloy $specifications:specification* end) =>
          let defaultBlockName := mkIdent (findDefaultName (← get).env)
          evalAlloyBlock defaultBlockName specifications

      | `(#alloy $blockName:separatedNamespace
            $specifications:specification* end) =>

            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace

            evalAlloyBlock
              (logging := true)
              blockName
              specifications

      | `(#alloy $blockName:separatedNamespace [$mvs:moduleVar,*]
            $specifications:specification* end) =>

            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace

            let moduleVariables :=
              (mvs.getElems.map
                fun mv =>
                (moduleVar.getIdent mv).getId.toString
              ).toList

            evalAlloyBlock
              (logging := true)
              (moduleVariables := moduleVariables)
              blockName
              specifications

      | `(#alloy module $blockName:separatedNamespace
            $specifications:specification* end) =>

            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace

            evalAlloyBlock
              (logging := true)
              blockName
              specifications

      | `(#alloy module $blockName:separatedNamespace [$mvs:moduleVar,*]
            $specifications:specification* end) =>

            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace

            let moduleVariables :=
              (mvs.getElems.map
                fun mv =>
                (moduleVar.getIdent mv).getId.toString
              ).toList

            evalAlloyBlock
              (logging := true)
              (moduleVariables := moduleVariables)
              blockName
              specifications

      | `(#alloy $specifications:specification* end) =>
            let defaultBlockName := mkIdent (findDefaultName (← get).env)
            evalAlloyBlock
              (logging := true)
              defaultBlockName
              specifications

      | `(~alloy $blockName:separatedNamespace
            $specifications:specification* end) =>
            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace
            Lean.Elab.Command.failIfSucceeds
              (evalAlloyBlock blockName specifications)

      | `(~alloy $blockName:separatedNamespace [$mvs:moduleVar,*]
            $specifications:specification* end) =>

            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace

            let moduleVariables :=
              (mvs.getElems.map
                fun mv =>
                (moduleVar.getIdent mv).getId.toString
              ).toList

            Lean.Elab.Command.failIfSucceeds
              (evalAlloyBlock
                (moduleVariables := moduleVariables)
                blockName
                specifications )

      | `(~alloy module $blockName:separatedNamespace
            $specifications:specification* end) =>
            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace
            Lean.Elab.Command.failIfSucceeds
              (evalAlloyBlock blockName specifications)

      | `(~alloy module $blockName:separatedNamespace [$mvs:moduleVar,*]
            $specifications:specification* end) =>

            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace

            let moduleVariables :=
              (mvs.getElems.map
                fun mv =>
                (moduleVar.getIdent mv).getId.toString
              ).toList

            Lean.Elab.Command.failIfSucceeds
              (evalAlloyBlock
                (moduleVariables := moduleVariables)
                blockName
                specifications)

      | `(~alloy $specifications:specification* end) =>
          let defaultBlockName := mkIdent (findDefaultName (← get).env)
          Lean.Elab.Command.failIfSucceeds
            (evalAlloyBlock defaultBlockName specifications)


      | _ => return -- if you enter # it might try to match and end here => do nothing

  catch | x => throwError x.toMessageData

syntax (name := creationSyntax) ("#" <|> "~")? "create" separatedNamespace : command

private def evaluateCreationCommand
  (ident : Ident)
  (logging : Bool)
  : CommandElabM Unit := do
    let monadeState ← get

    let dataName : Name := s!"{ident.getId.toString}_Data".toName
    let ads := getAlloyData monadeState.env

    if let Option.some (ad : alloyData) := ads.find? dataName then
      if logging then
        logInfo s!"Module data for {ident.getId.toString} found:\n\n {ad}"

      let st := ad.st
      let ast := ad.ast

      if !ast.modulVariables.isEmpty then
        logError s!"The module you tried to create has unbound module variables \n\
        ({ast.modulVariables})"

      else

        let except_commands := createCommands st
        match except_commands with
          | Except.error msg => throwError msg
          | Except.ok commands =>
              let mut commandString : String := ""

              for command in commands do
                elabCommand command
                commandString := s!"{commandString} {command.raw.prettyPrint} \n\n"

              if logging then
                logInfo commandString

              let it :=  InheritanceTree.create ast
              if logging then
                logInfo it.toString

              let extensionAxiomCommands :=
                it.createInheritanceAxiomCommands
                  (blockName := ident.getId)
                  st.getSignatureNames st.getSignatureRNames

              let mut extensionAxiomCommandsString := ""
              for axiomCommand in extensionAxiomCommands do
                elabCommand axiomCommand
                extensionAxiomCommandsString :=
                  s!"{extensionAxiomCommandsString} {axiomCommand.raw.prettyPrint} \n\n"

              if logging then
                logInfo extensionAxiomCommandsString

    else
      logError s!"Cannot create {ident.getId.toString}, it does not exist."


@[command_elab creationSyntax]
private def creationImpl : CommandElab := fun stx => do
  try
    match stx with
      | `(create $name:separatedNamespace) =>
        evaluateCreationCommand
          (separatedNamespace.toType name).representedNamespace
          false

      | `(#create $name:separatedNamespace) =>
        evaluateCreationCommand
          (separatedNamespace.toType name).representedNamespace
          true

      | `(~create $name:separatedNamespace) =>
        Lean.Elab.Command.failIfSucceeds
          (
            evaluateCreationCommand
              (separatedNamespace.toType name).representedNamespace
              false
          )

      | _ => return
  catch | x => throwError x.toMessageData
