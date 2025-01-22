/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.Rel
import ThoR.Relation.ElabCallMacro

import ThoR.Shared.Syntax.mult
import ThoR.Shared.Syntax.arrowOp

import ThoR.Shared.Syntax.TypeExpr.typeExpr
import ThoR.Shared.Syntax.TypeExpr.typeExprService

open Lean Lean.Elab Command Term
namespace ThoR

declare_syntax_cat rel_decl
syntax "(" ident " ∷ " typeExpr ")": rel_decl

open Shared

private def evaluateRelationDecl
  (rel_decls : Array (TSyntax `rel_decl))
  : CommandElabM Unit := do

    -- Sammlung aller Commands die ausgeführt werden sollen
    let mut allCmds : Array (TSyntax `command) := #[]

    -- jeden Syntaxeintrag auswerten der in der "Alloy-Sektion" vorhanden ist
    for rd in rel_decls do

      -- Sammlung der Commands aus einem Eintrag
      match rd with
      -- (subrel : te)
      | `(rel_decl| ( $subrel ∷ $te:typeExpr)) => do
        -- let cmd ← `(variable ($subrel : Nat))
        let typeExpression := (Shared.typeExpr.toType te)
        let type := typeExpression.toTermOutsideBlock
        let cmd ← `(variable ($subrel : $type))
--            let cmd ← `(variable ($subrel : $(mkIdent (Shared.typeExpr.toType te).toString)))
--            let cmd ← `(variable ($subrel : $(mkIdent (Shared.typeExpr.toType te).typeExprToTRel₀.toString)))
        allCmds := allCmds.push cmd
      | _ => continue -- FIX ME

    for command in allCmds do
      elabCommand command


elab "∷" t:typeExpr : term => do
      let typeExpression := (Shared.typeExpr.toType t)
      let type := typeExpression.toTermOutsideBlock
      elabTerm type Option.none

-- TODO: Variante von ∷ mit expliziter Angabe von R
--       Offener Punkt: Mit oder ohne @?
-- elab "@∷" rb:ident t:typeExpr : term => do
--       let typeExpression := (Shared.typeExpr.toType t)
--       let type := typeExpression.toTermOutsideBlock
--       elabTerm type Option.none

end ThoR
