/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/-
This file contains delaboration for all unRelOps, meaning
unary operations on relations.
-/

import Lean
import ThoR.Relation.Set
import ThoR.Alloy.Delab.DelaborationService

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander ThoR.HTransclos.hTransclos]
def unexpHTransclos : Unexpander
  | `($_ $param:ident) => do
    let new_param :=
      delaborationService.switch_thoR_representation_to_alloy_representation param
    `(^$new_param)

  | `($_ $param) => do
    `(^$param)

  | _ => throw Unit.unit

@[app_unexpander ThoR.HReflTransclos.hRTransclos]
def unexpHReflTransclos : Unexpander
  | `($_ $param:ident) => do
    let new_param :=
      delaborationService.switch_thoR_representation_to_alloy_representation param
    `(*$new_param)

  | `($_ $param) => do
    `(*$param)

  | _ => throw Unit.unit

@[app_unexpander ThoR.HTranspose.hTranspose]
def unexpHTranspose : Unexpander
  | `($_ $param:ident) => do
    let new_param :=
      delaborationService.switch_thoR_representation_to_alloy_representation param
    `(~$new_param)

  | `($_ $param) => do
    `(~$param)

  | _ => throw Unit.unit
