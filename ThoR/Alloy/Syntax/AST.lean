/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
This file is used to parse and precompile the alloy syntax.
-/
import ThoR.Basic

import ThoR.Alloy.Syntax.Signature
import ThoR.Alloy.Syntax.Predicate
import ThoR.Alloy.Syntax.assertDecl
import ThoR.Alloy.Syntax.factDecl
import ThoR.Alloy.Syntax.specification

open Lean
open Shared

namespace Alloy

/--
A structure representation of the abstract syntax tree (AST) of Alloy.
-/
inductive AST
  | mk  (name : String)
        (sigDecls : List (sigDecl))
        (factDecls : List (factDecl))
        (assertDecls : List (assertDecl))
        (predDecls : List (predDecl))
        (modulesToOpen : List (openModule))
        (openedModules : List (AST))
deriving Repr

namespace AST

  def name | mk name _ _ _ _ _ _ => name
  def sigDecls | mk _ sigDecls _ _ _ _ _ => sigDecls
  def factDecls | mk _ _ factDecls _ _ _ _ => factDecls
  def assertDecls | mk _ _ _ assertDecls _ _ _ => assertDecls
  def predDecls | mk _ _ _ _ predDecls _ _ => predDecls
  def modulesToOpen | mk _ _ _ _ _ modulesToOpen _ => modulesToOpen
  def openedModules | mk _ _ _ _ _ _ openedModules => openedModules

  instance : Inhabited AST where
    default :=
      AST.mk
        (name := default)
        (sigDecls := default)
        (factDecls := default)
        (assertDecls := default)
        (predDecls := default)
        (modulesToOpen := default)
        (openedModules := default)

  /--
  Generates a String representation of the AST
  -/
  partial def toString (ast : AST) : String := Id.run do
    let oms := ast.openedModules.map fun om => toString om

    s!"AST : \{
        name := {ast.name},
        sigDecls := {ast.sigDecls},
        factDecls := {ast.factDecls},
        assertDecls := {ast.assertDecls},
        predDecls := {ast.predDecls},
        modules to open := {ast.modulesToOpen},
        opened modules := {oms}
      }"

  instance : ToString AST where
  toString ( ast : AST ) : String := toString ast

  /--
  Updates the name of the AST to the given value
  -/
  def updateName (name : String)
    | mk _ sigDecls factDecls assertDecls
      predDecls modulesToOpen openendModules =>
        AST.mk name sigDecls factDecls assertDecls
        predDecls modulesToOpen openendModules

  /--
  Clears the modules to open from the AST
  -/
  def clearModulesToOpen
    | mk name sigDecls factDecls assertDecls
      predDecls _ openendModules =>
        AST.mk name sigDecls factDecls assertDecls
        predDecls default openendModules

  /--
  Adds a single `sigDecl` to the AST
  -/
  def addSigDecl (sd : sigDecl)
    | mk name sigDecls factDecls assertDecls
      predDecls modulesToOpen openendModules =>
        AST.mk name (sigDecls.concat sd) factDecls assertDecls
        predDecls modulesToOpen openendModules

  /--
  Adds a single `factDecl` to the AST
  -/
  def addFactDecl (fd : factDecl)
    | mk name sigDecls factDecls assertDecls
      predDecls modulesToOpen openendModules =>
        AST.mk name sigDecls (factDecls.concat fd) assertDecls
        predDecls modulesToOpen openendModules

  /--
  Adds a single `assertDecl` to the AST
  -/
  def addAssertDecl (ad : assertDecl)
    | mk name sigDecls factDecls assertDecls
      predDecls modulesToOpen openendModules =>
        AST.mk name sigDecls factDecls (assertDecls.concat ad)
        predDecls modulesToOpen openendModules

  /--
  Adds a single `predDecl` to the AST
  -/
  def addPredDecl (pd : predDecl)
    | mk name sigDecls factDecls assertDecls
      predDecls modulesToOpen openendModules =>
        AST.mk name sigDecls factDecls assertDecls
        (predDecls.concat pd) modulesToOpen openendModules

  /--
  Adds a single module to open (`openModule`) to the AST
  -/
  def addModuleToOpen (om : openModule)
    | mk name sigDecls factDecls assertDecls
      predDecls modulesToOpen openendModules =>
        AST.mk name sigDecls factDecls assertDecls
        predDecls (modulesToOpen.concat om) openendModules

  /--
  Adds a single opened module (`AST`) to the AST
  -/
  def addOpenedModule (ast : AST) (om : AST) : AST :=
    match ast with
      | mk name sigDecls factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name sigDecls factDecls assertDecls
          predDecls modulesToOpen (openendModules.concat om)

  /--
  Creates an AST from a name and an array of `specifications`
  -/
  def create
    (name : Ident)
    (specifications : Array (TSyntax `specification))
    : AST := Id.run do

      let mut ast : AST := (default)
      ast := ast.updateName name.getId.toString

      -- used for default fact name
      let mut factCount := 0

      for spec in specifications do
        match spec with

        --signature WITH signatureFact
        | `(specification| $sd:sigDecl $sf:signatureFactDecl) =>
          let sigDeclTyped := sigDecl.toType sd
          ast := ast.addSigDecl sigDeclTyped

          let signatureNames : List String := sigDeclTyped.names
          let signatureRelationNames : List String :=
            (sigDeclTyped.fieldDecls.map fun fd => fd.names).join

          -- create a fact per created signature
          for signatureName in signatureNames do
            let defaultName : String := s!"f{factCount}"

            let factDecl :=
              (signatureFactDecl.toType defaultName sf
                signatureName signatureRelationNames)

            ast := ast.addFactDecl factDecl

            --icrease factcounter accordingly
            factCount := factCount + 1

        --signature
        | `(specification| $sd:sigDecl) =>
          ast := ast.addSigDecl (sigDecl.toType sd)


        --fact
        | `(specification| $fd:factDecl) =>
          let defaultName : String := s!"f{factCount}"
          -- factDecl.toType:
          -- - fact without fact names: set default fact name (f0, f1, ...)
          -- - fact with fact name: keep fact name
          let newFactDecl := factDecl.toType defaultName fd
          if newFactDecl.name == defaultName then factCount := factCount + 1
          ast := ast.addFactDecl newFactDecl

        --assert
        | `(specification| $ad:assertDecl) =>
          ast := ast.addAssertDecl (assertDecl.toType ad)

        --Predicate
        | `(specification| $pd:predDecl) =>
          ast := ast.addPredDecl (predDecl.toType pd)

        -- Open Module
        | `(specification| $om:openModule) =>
          ast := ast.addModuleToOpen (openModule.toType om)

        | _ => continue

      return ast

  /--
  Concatenates two abstact syntax trees.
  The resulting AST takes the name of the first given AST.
  -/
  def concat (ast1 ast2 : AST) : AST :=
    match ast1, ast2 with
      | mk name1 sigDecls1 factDecls1 assertDecls1
        predDecls1 modulesToOpen1 openendModules1,
        mk _ sigDecls2 factDecls2 assertDecls2
        predDecls2 modulesToOpen2 openendModules2
        =>
        mk name1
          (sigDecls1.append sigDecls2)
          (factDecls1.append factDecls2)
          (assertDecls1.append assertDecls2)
          (predDecls1.append predDecls2)
          (modulesToOpen1.append modulesToOpen2)
          (openendModules1.append openendModules2)

end AST

end Alloy
