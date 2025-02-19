/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.Set
import ThoR.Alloy.Delab.DelaborationService

open Lean PrettyPrinter Delaborator SubExpr Expr
open ThoR

@[app_unexpander ThoR.HEqual.hEqual]
def unexpHEqual : Unexpander
  | `($_ $a:ident $b:ident) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($new_a = $new_b)

  | `($_ $a:ident $b) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    `($new_a = $b)

  | `($_ $a $b:ident) =>
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($a = $new_b)

  | `($_ $a $b) =>
    `($a = $b)

  | _ => throw Unit.unit

@[app_unexpander ThoR.HNEqual.hNEqual]
def unexpHNEqual : Unexpander
  | `($_ $a:ident $b:ident) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($new_a != $new_b)

  | `($_ $a:ident $b) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    `($new_a != $b)

  | `($_ $a $b:ident) =>
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($a != $new_b)

  | `($_ $a $b) =>
    `($a != $b)

  | _ => throw Unit.unit

@[app_unexpander ThoR.HSubset.hSubset]
def unexpHSubset : Unexpander
  | `($_ $a:ident $b:ident) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($new_a $(mkIdent `in) $new_b)

  | `($_ $a:ident $b) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    `($new_a $(mkIdent `in) $b)

  | `($_ $a $b:ident) =>
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($a $(mkIdent `in) $new_b)

  | `($_ $a $b) =>
    `($a $(mkIdent `in) $b)

  | _ => throw Unit.unit
