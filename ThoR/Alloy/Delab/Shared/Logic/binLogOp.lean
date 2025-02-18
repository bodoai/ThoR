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

@[app_unexpander And]
def unexpandAnd : Unexpander
  | `($_ $a:ident $b:ident) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($new_a $(mkIdent `and) $new_b)

  | `($_ $a:ident $b) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    `($new_a $(mkIdent `and) $b)

  | `($_ $a $b:ident) =>
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($a $(mkIdent `and) $new_b)

  | `($_ $a $b) =>
    `($a $(mkIdent `and) $b)

  | _ => throw Unit.unit

@[app_unexpander Or]
def unexpandOr : Unexpander
  | `($_ $a:ident $b:ident) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($new_a $(mkIdent `or) $new_b)

  | `($_ $a:ident $b) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    `($new_a $(mkIdent `or) $b)

  | `($_ $a $b:ident) =>
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($a $(mkIdent `or) $new_b)

  | `($_ $a $b) =>
    `($a $(mkIdent `or) $b)

  | _ => throw Unit.unit

@[app_unexpander Iff]
def unexpandIff : Unexpander
  | `($_ $a:ident $b:ident) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($new_a $(mkIdent `iff) $new_b)

  | `($_ $a:ident $b) =>
    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    `($new_a $(mkIdent `iff) $b)

  | `($_ $a $b:ident) =>
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b
    `($a $(mkIdent `iff) $new_b)

  | `($_ $a $b) =>
    `($a $(mkIdent `iff) $b)

  | _ => throw Unit.unit
