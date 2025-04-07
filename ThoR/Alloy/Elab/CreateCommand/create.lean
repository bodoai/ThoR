/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.SeparatedNamespace
import ThoR.Alloy.Syntax.AlloyData.alloyData
import ThoR.Alloy.Syntax.AlloyData.alloyDataService
import ThoR.Alloy.Elab.CreateCommand.createService
import ThoR.Alloy.InheritanceTree.UnTyped.InheritanceTree

open Lean Lean.Elab Command Term

namespace Alloy

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

        if ad.isCreated then
          logError s!"The module has already been created."
          return

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

              let newMonadeEnv :=
              updateAlloyData (← getEnv) {ad with isCreated := true}

              match newMonadeEnv with
                | Except.ok nme => setEnv nme
                | Except.error msg => logError s!"Failed to set the alloy data \
                to created: {msg}"

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

end Alloy
