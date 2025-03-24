/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.AST.AST
import ThoR.Alloy.Syntax.Predicate.PredDecl.predDeclService
import ThoR.Alloy.Syntax.FactDecl.factDeclService
import ThoR.Alloy.Syntax.AssertDecl.assertDeclService
import ThoR.Alloy.Syntax.Signature.SignatureFactDecl.signatureFactDeclService
import ThoR.Alloy.Syntax.Function.FunctionDecl.functionDeclService

open Lean

namespace Alloy.AST

  /--
  Creates an AST from a name and an array of `specifications`
  -/
  def create
    (name : Ident)
    (specifications : Array Specification)
    (moduleVariables : List (String))
    : AST := Id.run do

      let mut ast : AST := (default)
      ast := ast.updateName name.getId

      ast := ast.updateModuleVariables moduleVariables

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

        -- function
        | `(specification | $fd:functionDecl) =>
          ast := ast.addFunctionDecl (functionDecl.toType fd)

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

end Alloy.AST
