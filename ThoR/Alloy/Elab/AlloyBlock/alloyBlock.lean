/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.SeparatedNamespace
import ThoR.Alloy.Syntax.alloyData
import ThoR.Alloy.Syntax.OpenModule.openModuleHelper
import ThoR.Alloy.Syntax.Signature.SigDecl.sigDeclService

import ThoR.Alloy.SymbolTable.SymbolTableService

import ThoR.Alloy.Elab.AlloyBlock.moduleVar

open ThoR Shared Config
open Lean Lean.Elab Command Term

namespace Alloy

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

end Alloy
