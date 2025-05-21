/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.AST.AST
import ThoR.Alloy.SymbolTable.SymbolTable
import ThoR.Alloy.SymbolTable.SymbolTableService

open ThoR Shared Config
open Lean

namespace Alloy

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
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
    : Except String Command := do

      -- formula evaluation
      -- All formulas (lines) in an Alloy pred or in an Alloy fact are
      -- transformed into a conjunction of all these formulas.
      let emptyTerm : Term :=
        unhygienicUnfolder `(term | $(mkIdent `error.in.creation.service))
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
          ff.toSemanticsTerm
            blockName cd.requiredVars callableVariables cd.predCalls argnames

        for formula in forms.drop 1 do
          let newTerm ←
            formula.toSemanticsTerm
              blockName cd.requiredVars callableVariables cd.predCalls argnames
          bodyTerm := unhygienicUnfolder `($bodyTerm ∧ ($newTerm))

      -- function only has expressions
      if cd.isFunction && !(cd.expressions.isEmpty) then
        let expressions :=
          cd.expressions.map fun e => e.replaceCalls callableVariables

        let argNames := (cd.functionArgs.map fun fa => fa.1.names).join

        let fe := (expressions.get! 0)
        bodyTerm ← fe.toTerm blockName cd.requiredVars callableVariables cd.predCalls argNames

        for expression in expressions.drop 1 do
          let newTerm ←
            expression.toTerm blockName cd.requiredVars
              callableVariables cd.predCalls argNames

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
            let typeTerm ← type.toSemanticsTerm blockName
              cd.requiredVars callableVariables cd.predCalls
            let names := (arg.1.names.map fun name => (mkIdent name.toName)).toArray

            for name in names do
              bodyTerm := unhygienicUnfolder `( term |
                (
                  $(mkIdent ``ThoR.Semantics.Term.lam)
                  ($(mkIdent `R) := $(baseType.ident))
                  ( λ ( $(name) : ($(typeTerm) : Type)) => $bodyTerm )
                )
              )

        -- function arguments
        if cd.isFunction && !(cd.functionArgs.isEmpty) then
          for arg in cd.functionArgs do
            let type := (arg.1.type.replaceCalls callableVariables)
            let typeTerm ← type.toSemanticsTerm blockName
              cd.requiredVars callableVariables cd.predCalls

            let names := (arg.1.names.map fun name => (mkIdent name.toName)).toArray

            for name in names do
              bodyTerm := unhygienicUnfolder `( term |
                (
                  $(mkIdent ``ThoR.Semantics.Term.lam)
                  ($(mkIdent `R) := $(baseType.ident))
                  ( λ ( $(name) : ($(typeTerm) : Type)) => $bodyTerm )
                )
              )

        -- add function arguments and function return type
        if cd.isFunction then
          let returnType :=
            (cd.functionReturnType.replaceCalls callableVariables).toStringRb
          let returnTypeSyntax := returnType.toSyntax blockName
          let argNames := (cd.functionArgs.map fun fa => fa.1.names).join
          let returnTypeTerm ← returnType.toTerm blockName cd.requiredVars callableVariables cd.predCalls argNames
          argTerms := unhygienicUnfolder
            `(Lean.Parser.Command.optDeclSig| $[$allArgs]* : ∷ $returnTypeSyntax)


          bodyTerm := unhygienicUnfolder `(cast ($(bodyTerm)) ∷ $returnTypeTerm)

        if bodyTerm != emptyTerm then
          return unhygienicUnfolder `(
            def $(mkIdent cd.name.toName)
            $argTerms
            :=
            $(
              if cd.isFunction then
                (mkIdent ``ThoR.Semantics.Term.fun_def)
              else
                (mkIdent ``ThoR.Semantics.Term.pred_def)
            )
            $bodyTerm
          )
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
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
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
          let cdCmd ← (createDefOrAxiomCommand blockName cd callableVariables callablePredicates)
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
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
    : Except String (List Command) :=
      createDefsCommandsWithNamespace
        (namespaceName := s!"{blockName}.preds".toName)
        blockName defDecls callableVariables callablePredicates

  /--
  Creates commands to create Lean definitions (for functions) from the given
  blockname and commandDecls.

  The created commands are encapsulated in a namespace named blockname.functions
  -/
  private def createFunctionDefsCommands
    (blockName : Name)
    (defDecls : List (commandDecl))
    (callableVariables : List (varDecl))
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
    : Except String (List ((TSyntax `command))) :=
      createDefsCommandsWithNamespace
        (namespaceName := s!"{blockName}.functions".toName)
        blockName defDecls callableVariables callablePredicates

  /--
  Creates commands to create Lean definitions (for asserts) from the given
  blockname and commandDecls.

  The created commands are encapsulated in a namespace named blockname.asserts
  -/
  private def createAssertDefsCommands
    (blockName : Name)
    (defDecls : List (commandDecl))
    (callableVariables : List (varDecl))
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
    : Except String (List Command) :=
      createDefsCommandsWithNamespace
        (namespaceName := s!"{blockName}.asserts".toName)
        blockName  defDecls callableVariables callablePredicates

  /--
  Creates commands to create Lean axioms from the given blockname and commandDecls.

  The created commands are encapsulated in a namespace named blockname.facts
  -/
  private def createAxiomCommands
    (blockName : Name)
    (axiomDecls : List (commandDecl))
    (callableVariables : List (varDecl))
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
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
          let adCmd ← (createDefOrAxiomCommand blockName ad callableVariables callablePredicates)
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
  def createCommands
    (st : SymbolTable)
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

      let callablePredicates := (st.getPredicateDeclarations.map fun pd => pd.predCalls).join

      -- predicates
      let predCommands ← createPredDefsCommands blockName (st.defDecls.filter fun dd => dd.isPredicate) st.variableDecls callablePredicates
      commandList := commandList.append predCommands
      if !(predCommands.isEmpty) then
        namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.preds".toName)

      -- functions
      let functionCommands ← createFunctionDefsCommands blockName (st.defDecls.filter fun dd => dd.isFunction) st.variableDecls callablePredicates
      commandList := commandList.append functionCommands
      if !(functionCommands.isEmpty) then
        namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.functions".toName)

      -- axioms
      let axCommands ← createAxiomCommands blockName st.axiomDecls st.variableDecls callablePredicates
      commandList := commandList.append axCommands
      if !(axCommands.isEmpty) then
        namespacesToOpen := namespacesToOpen.push (mkIdent s!"{blockName}.facts".toName)

      -- asserts
      let assertCommands ← createAssertDefsCommands blockName st.assertDecls st.variableDecls callablePredicates
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

end Alloy
