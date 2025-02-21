/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.Set
import ThoR.Alloy.Delab.DelaborationService
import ThoR.Shared.Syntax.Logic.terLogOp

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander Shared.terLogOp.myIfElse]
def unexpHTransclos : Unexpander
  | `($_ $a:ident $b:ident $c:ident) => do
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    let new_c :=
      delaborationService.switch_thoR_representation_to_alloy_representation c
    `($(mkIdent `if) $new_a $(mkIdent `then) $new_b $(mkIdent `else) $new_c)

  | `($_ $a:ident $b:ident $c) => do
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($(mkIdent `if) $new_a $(mkIdent `then) $new_b $(mkIdent `else) $c)

  | `($_ $a:ident $b $c:ident) => do
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    let new_c :=
      delaborationService.switch_thoR_representation_to_alloy_representation c
    `($(mkIdent `if) $new_a $(mkIdent `then) $b $(mkIdent `else) $new_c)

  | `($_ $a:ident $b $c) => do
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    `($(mkIdent `if) $new_a $(mkIdent `then) $b $(mkIdent `else) $c)

  | `($_ $a $b:ident $c:ident) => do
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    let new_c :=
      delaborationService.switch_thoR_representation_to_alloy_representation c
    `($(mkIdent `if) $a $(mkIdent `then) $new_b $(mkIdent `else) $new_c)

  | `($_ $a $b:ident $c) => do
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($(mkIdent `if) $a $(mkIdent `then) $new_b $(mkIdent `else) $c)

  | `($_ $a $b $c:ident) => do
    let new_c :=
      delaborationService.switch_thoR_representation_to_alloy_representation c
    `($(mkIdent `if) $a $(mkIdent `then) $b $(mkIdent `else) $new_c)

  | `($_ $a $b $c) => do
    `($(mkIdent `if) $a $(mkIdent `then) $b $(mkIdent `else) $c)

  | _ => throw Unit.unit
