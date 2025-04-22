/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the data structures-/
import ThoR.Shared.Syntax.Mutuals.mutuals

import ThoR.Alloy.UnhygienicUnfolder
import ThoR.Relation.ElabCallMacro
import ThoR.Alloy.Syntax.AlloyData.alloyData
import ThoR.Alloy.Config
import Lean

open Lean
open Alloy Config

namespace Shared

  mutual

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

  end

end Shared
