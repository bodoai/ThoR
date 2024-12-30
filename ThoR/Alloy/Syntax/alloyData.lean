/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Alloy.Syntax.AST
import ThoR.Alloy.SymbolTable

open ThoR Shared Alloy
open Lean Lean.Elab Command Term

/-
All needed Data to create Alloy Commands
-/
namespace Alloy

  structure alloyData where
    (ast : AST)
    (st : SymbolTable)

  namespace alloyData
    def toTerm (ad : alloyData) : TSyntax `term := Unhygienic.run do
      let astTerm := ad.ast.toTerm
      let stTerm := ad.st.toTerm

      return ← `(({ast := $(astTerm), st := $(stTerm)} : Alloy.alloyData ))

    instance : ToString alloyData where
      toString ( ad : alloyData ) : String :=
        s!"AlloyData : \{
            abstract syntax tree := {ad.ast},
            symbol table := {ad.st}
          }"

    instance : Inhabited alloyData where
      default := {ast := default, st := default}

  end alloyData

  abbrev alloyDataState := NameMap alloyData

  abbrev AlloyDataExtension :=
    SimplePersistentEnvExtension alloyData alloyDataState

  def alloyDataState.addEntry
    (s : alloyDataState)
    (ad : alloyData)
    : NameMap alloyData :=
      s.insert (s!"{ad.ast.name}_Data".toName) ad

  initialize alloyDataExtension : AlloyDataExtension ←
    registerSimplePersistentEnvExtension {
      addImportedFn :=
        mkStateFromImportedEntries alloyDataState.addEntry {}

      addEntryFn    := alloyDataState.addEntry
    }

  def getAlloyData
    (env : Environment)
    : alloyDataState :=
      alloyDataExtension.getState env

  def addAlloyData
    (env : Environment)
    (ad : alloyData)
    : Except String Environment := do
      let ad' := (getAlloyData env).find? s!"{ad.ast.name}_Data".toName
      if ad'.isSome then
        let ads' := ad'.get!
        if ads'.ast.name == ad.ast.name then
          throw s!"There is already an extension with the \
          name {ad.ast.name}. Could not create the environment \
          extension"
        return env
      else
        return alloyDataExtension.addEntry env ad

end Alloy
