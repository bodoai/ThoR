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

import ThoR.Alloy.Syntax.AST
import ThoR.Alloy.SymbolTable
import ThoR.Alloy.InheritanceTree.UnTyped.InheritanceTree
import ThoR.Alloy.Syntax.SeparatedNamespace
import ThoR.Alloy.Syntax.alloyData

open ThoR Shared Alloy
open Lean Lean.Elab Command Term

/--
Creates commands to create all variables from the given variable declarations and the block name.

The created vars are inside a namespace named blockname and inside a type class
named var.
-/
private def createVariableCommands
  (blockName : Name)
  (variableDecls : List (varDecl))
  : List ((TSyntax `command)) := Unhygienic.run do
    let mut commandList : List ((TSyntax `command)) := []

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
        let varField ←
          `(Lean.Parser.Command.structExplicitBinder |
              ($(mkIdent vd.name.toName) :
                ∷ $(vd.type.toSyntax blockNameIdent.getId)))

        variableFields := variableFields.push varField

      let id : Ident := mkIdent "vars".toName
      let mut variableTypeclass : TSyntax `command ←
      `(class $id ($baseType.getIdent : Type) [$(mkIdent ``ThoR.TupleSet) $baseType.getIdent] where
          $[$variableFields]*
        )
      commandList := commandList.concat variableTypeclass

      --NamespaceEnd
      commandList := commandList.concat (← `(end $blockNameIdent))

      return commandList

/--
Creates a single creation command of either a definition or an axiom from a
given command declaration and the blockname.

Whether a definition or an axiom is created is determined by the definition parameter.
(definition=true -> def, definition=false -> axiom)
-/
private def createDefOrAxiomCommand
  (blockName : Name)
  (cd : commandDecl)
  (definition : Bool)
  : Option (TSyntax `command) := Unhygienic.run do

    -- formula evaluation
    -- All formulas (lines) in an Alloy pred or in an Alloy fact are
    -- transformed into a conjunction of all these formulas.
    let emptyTerm : TSyntax `term ← `($(mkIdent "".toName))
    let mut bodyTerm : TSyntax `term := emptyTerm


    if !(cd.formulas.isEmpty) then

      let argnames := (cd.args.map fun (arg) => arg.names).join

      let ff := (cd.formulas.get! 0)

      bodyTerm : TSyntax `term ←
        `($(ff.toTerm blockName cd.requiredVars argnames))

      for formula in cd.formulas.drop 1 do
        let newTerm ← `($(formula.toTerm blockName cd.requiredVars argnames))
        bodyTerm ←
          `($bodyTerm ∧ ($newTerm))

    -- Alloy pred argument evaluation
    -- (no arguments for definition=false, as facts do not have any arguments)
    -- Alloy pred arguments are transformed into Lean function arguments.
    let mut argTerms : TSyntax ``Lean.Parser.Command.optDeclSig ←
      `(Lean.Parser.Command.optDeclSig|)

    if !(cd.args.isEmpty) then
      for arg in cd.args do
        let mut singleArg :
          Array (TSyntax ``Lean.Parser.Term.bracketedBinderF) := #[]
        let mut names : Array (TSyntax `ident) := #[]

        let t :=
          (typeExpr.relExpr
            arg.expression.toStringRb).toSyntax blockName

        for name in arg.names do
          names := names.push (mkIdent name.toName)

        let argTerm ← `(Lean.Parser.Term.bracketedBinderF |
          ($[$names]* : ∷ $t))

        singleArg := singleArg.push argTerm

        argTerms ← `(Lean.Parser.Command.optDeclSig| $[$singleArg]*)

    -- define command
    if definition then
      if bodyTerm != emptyTerm then
        return ← `(def $(mkIdent cd.name.toName) $argTerms := $bodyTerm)
      else
        return ← `(
          def $(mkIdent cd.name.toName)
          ($(baseType.getIdent) : Type)
          [$(mkIdent ``ThoR.TupleSet) $(baseType.getIdent)]
          [$(mkIdent s!"{blockName}.vars".toName) $(baseType.getIdent)]
          := True )
    else
    -- axiom command
      if bodyTerm != emptyTerm then
        return ← `(axiom $(mkIdent cd.name.toName) : $bodyTerm)
      else
        return ← `(
          axiom $(mkIdent cd.name.toName)
          ($(baseType.getIdent) : Type)
          [$(mkIdent ``ThoR.TupleSet) $(baseType.getIdent)]
          [$(mkIdent s!"{blockName}.vars".toName) $(baseType.getIdent)]
          : True )



/--
convenience function:
Creates a single command which creates a definition from the given
blockname and command declaration.
-/
private def createDefCommand
  (blockName : Name)
  (cd : commandDecl)
  : Option (TSyntax `command) :=
    createDefOrAxiomCommand blockName cd true

/--
convenience function:
Creates a single command which creates an axiom from the given
blockname and command declaration.
-/
private def createAxiomCommand
  (blockName : Name)
  (cd : commandDecl)
  : Option (TSyntax `command) :=
    createDefOrAxiomCommand blockName cd false

/--
Creates commands to create Lean definitions from the given blockname and commandDecls.

The created commands are encapsulated in a namespace with the given Name
-/
private def createDefsCommandsWithNamespace
  (blockName : Name)
  (namespaceName : Name)
  (commandDecls : List (commandDecl))
  :List ((TSyntax `command) ) := Unhygienic.run do
    let mut commandList : List ((TSyntax `command) ) := []

    if commandDecls.isEmpty then
      return commandList
    else

      --NamespaceBegin
      commandList := commandList.concat
        ( ← `(namespace $(mkIdent namespaceName)))

      --BaseTypeDecl
      let defsBaseType : TSyntax `command ←
      `(variable {$baseType.getIdent : Type}
        [$(mkIdent ``ThoR.TupleSet) $baseType.getIdent]
        [$(mkIdent (s!"{blockName}.vars").toName) $baseType.getIdent])

      commandList := commandList.concat defsBaseType

      --Def declaration
      for cd in commandDecls do
        let cdCmd := (createDefCommand blockName cd)
        if cdCmd.isSome then
          commandList := commandList.concat cdCmd.get!

      --NamespaceEnd
      commandList := commandList.concat
        (← `(end $(mkIdent namespaceName)))

      return commandList

/--
Creates commands to create Lean definitions (for preds) from the given
blockname and commandDecls.

The created commands are encapsulated in a namespace named blockname.preds
-/
private def createPredDefsCommands
  (blockName : Name)
  (defDecls : List (commandDecl))
  :List ((TSyntax `command) ) :=
    createDefsCommandsWithNamespace blockName (s!"{blockName}.preds".toName) defDecls

/--
Creates commands to create Lean definitions (for asserts) from the given
blockname and commandDecls.

The created commands are encapsulated in a namespace named blockname.asserts
-/
private def createAssertDefsCommands
  (blockName : Name)
  (defDecls : List (commandDecl))
  :List ((TSyntax `command) ) :=
    createDefsCommandsWithNamespace blockName (s!"{blockName}.asserts".toName) defDecls

/--
Creates commands to create Lean axioms from the given blockname and commandDecls.

The created commands are encapsulated in a namespace named blockname.facts
-/
private def createAxiomCommands
  (blockName : Name)
  (axiomDecls : List (commandDecl))
  :List ((TSyntax `command)) := Unhygienic.run do
    let mut commandList : List ((TSyntax `command)) := []

    if axiomDecls.isEmpty then
      return commandList
    else

      let namespaceName := (s!"{blockName}.facts").toName

      --NamespaceBegin
      commandList := commandList.concat
        (← `(namespace $(mkIdent namespaceName)))

      --BaseTypeDecl
      let defsBaseType : TSyntax `command ←
      `(variable {$(baseType.getIdent) : Type}
        [$(mkIdent ``ThoR.TupleSet) $(baseType.getIdent)]
        [$(mkIdent (s!"{blockName}.vars").toName) $(baseType.getIdent)])

      commandList := commandList.concat defsBaseType

      --Axiom declaration
      for ad in axiomDecls do
       let adCmd := (createAxiomCommand blockName ad)
        if adCmd.isSome then
          commandList := commandList.concat adCmd.get!

      --NamespaceEnd
      commandList := commandList.concat
        (← `(end $(mkIdent namespaceName)))

      return commandList

/--
Creates commands to create all variables, definitions and axioms in Lean.

The created commands are encapsulated in a namespaces, which are opened as the last command.
-/
private def createCommands (st : SymbolTable)
  : List ((TSyntax `command)) := Unhygienic.run do

    let blockName : Name := st.blockName.toName
    let mut namespacesToOpen : Array (Ident) := #[]

    --variables
    let mut commandList : List ((TSyntax `command)) := []

    let varCommands := createVariableCommands blockName st.variableDecls
    commandList := commandList.append varCommands
    if !(varCommands.isEmpty) then
      namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.vars".toName)

    -- defs
    let defCommands := createPredDefsCommands blockName st.defDecls
    commandList := commandList.append defCommands
    if !(defCommands.isEmpty) then
      namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.preds".toName)

    -- axioms
    let axCommands := createAxiomCommands blockName st.axiomDecls
    commandList := commandList.append axCommands
    if !(axCommands.isEmpty) then
      namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.facts".toName)

    -- asserts
    let assertCommands := createAssertDefsCommands blockName st.assertDecls
    commandList := commandList.append assertCommands
    if !(assertCommands.isEmpty) then
      namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.asserts".toName)

    -- open the namespaces to use all withot explicit calling
    let openDecl : TSyntax `Lean.Parser.Command.openDecl ←
      `(Lean.Parser.Command.openDecl|
        $[$(namespacesToOpen)]*
      )
    commandList := commandList.concat (← `(open $openDecl))

    return commandList

/--
Represents the syntax for the alloy block.

Options:
- To get a logoutput: #alloy
- To succeed on failure (with the exception of syntax errors): ~alloy
-/
syntax (name := alloyBlock)
  ("#" <|> "~")? "alloy " (("module")? separatedNamespace)? specification* " end" : command

/--
Evaluates the alloy block syntax.
-/
private def evalAlloyBlock
  (name : Ident)
  (specifications : Array (TSyntax `specification))
  (logging: Bool)
  : CommandElabM Unit := do

    let ast := AST.create name specifications
    if logging then
      logInfo (ast.toString)

    let result := SymbolTable.create ast
    let st := result.1

    let check := result.2
    let allChecksCorrect := check.1
    let checkMsg := check.2
    if logging then
      logInfo (st.toString)

    if !allChecksCorrect then
      logError (checkMsg)

    else

      let data : alloyData := {ast := ast, st := st}
      let dataName := name
      let dataCommand ←
        `(def $dataName : alloyData := $(data.toTerm))
      elabCommand dataCommand
      if logging then
        logInfo s!"{dataCommand.raw.prettyPrint}"

      /-
      let commands := createCommands st

      let mut commandString : String := ""

      for command in commands do
        elabCommand command
        commandString := s!"{commandString} {command.raw.prettyPrint} \n\n"

      if logging then
        logInfo commandString

      let it :=  InheritanceTree.create ast
      if logging then
        logInfo it.toString

      let extensionAxiomCommands := it.createAxiomsCommand name.getId
      let mut extensionAxiomCommandsString := ""
      for axiomCommand in extensionAxiomCommands do
        elabCommand axiomCommand
        extensionAxiomCommandsString :=
          s!"{extensionAxiomCommandsString} {axiomCommand.raw.prettyPrint} \n\n"

      if logging then
        logInfo extensionAxiomCommandsString
      -/

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
          evalAlloyBlock blockName specifications false

      | `(alloy module $blockName:separatedNamespace
            $specifications:specification* end) =>
          let blockName :=
            (separatedNamespace.toType blockName).representedNamespace
          evalAlloyBlock blockName specifications false

      | `(alloy $specifications:specification* end) =>
          let defaultBlockName := mkIdent (findDefaultName (← get).env)
          evalAlloyBlock defaultBlockName  specifications false

      | `(#alloy $blockName:separatedNamespace
            $specifications:specification* end) =>
            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace
            evalAlloyBlock blockName specifications true

      | `(#alloy module $blockName:separatedNamespace
            $specifications:specification* end) =>
            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace
            evalAlloyBlock blockName specifications true

      | `(#alloy $specifications:specification* end) =>
            let defaultBlockName := mkIdent (findDefaultName (← get).env)
            evalAlloyBlock defaultBlockName specifications true

      | `(~alloy $blockName:separatedNamespace
            $specifications:specification* end) =>
            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace
            Lean.Elab.Command.failIfSucceeds
              (evalAlloyBlock blockName specifications false)

      | `(~alloy module $blockName:separatedNamespace
            $specifications:specification* end) =>
            let blockName :=
              (separatedNamespace.toType blockName).representedNamespace
            Lean.Elab.Command.failIfSucceeds
              (evalAlloyBlock blockName specifications false)

      | `(~alloy $specifications:specification* end) =>
          let defaultBlockName := mkIdent (findDefaultName (← get).env)
          Lean.Elab.Command.failIfSucceeds
            (evalAlloyBlock defaultBlockName specifications false)


      | _ => return -- if you enter # it might try to match and end here => do nothing

  catch | x => throwError x.toMessageData

syntax (name := creationSyntax) ("#")? "create" ident : command

private def evaluateCreationCommand
  (name : Ident)
  (logging : Bool)
  : CommandElabM Unit := do
    let env ← get
    env.env.displayStats

@[command_elab creationSyntax]
private def creationImpl : CommandElab := fun stx => do
  try
    match stx with
      | `(create $name:ident) => evaluateCreationCommand name false
      | _ => return
  catch | x => throwError x.toMessageData
