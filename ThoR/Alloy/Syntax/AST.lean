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
structure AST where
  mk :: (name : String)
        (sigDecls : List (sigDecl))
        (factDecls : List (factDecl))
        (assertDecls : List (assertDecl))
        (predDecls : List (predDecl))
deriving Repr

instance : ToString AST where
  toString ( ast : AST ) : String :=
    s!"AST : \{
        name := {ast.name},
        sigDecls := {ast.sigDecls},
        factDecls := {ast.factDecls},
        assertDecls := {ast.assertDecls},
        predDecls := {ast.predDecls}
      }"

instance : Inhabited AST where
  default := {
    name := default,
    sigDecls := default,
    factDecls := default,
    assertDecls := default,
    predDecls := default
  }

namespace AST

  /--
  Generates a String representation of the AST
  -/
  def toString (ast : AST) : String := ToString.toString ast

  /--
  Adds a single `sigDecl` to the AST
  -/
  def addSigDecl (ast : AST) (sd : sigDecl) : AST :=
    {ast with sigDecls := ast.sigDecls.concat sd}

  /--
  Adds a single `factDecl` to the AST
  -/
  def addFactDecl (ast : AST) (fd : factDecl) : AST :=
    {ast with factDecls := ast.factDecls.concat fd}

  /--
  Adds a single `assertDecl` to the AST
  -/
  def addAssertDecl (ast : AST) (ad : assertDecl) : AST :=
    {ast with assertDecls := ast.assertDecls.concat ad}

  /--
  Adds a single `predDecl` to the AST
  -/
  def addPredDecl (ast : AST) (pd : predDecl) : AST :=
    {ast with predDecls := ast.predDecls.concat pd}

  /--
  Creates an AST from a name and an array of `specifications`
  -/
  def create
    (name : Ident)
    (specifications : Array (TSyntax `specification))
    : AST := Id.run do

      let mut ast : AST := {
        name := name.getId.lastComponentAsString
        sigDecls := []
        factDecls := []
        assertDecls := []
        predDecls := []
      }

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

        | _ => unreachable!

      return ast

  end AST

end Alloy
