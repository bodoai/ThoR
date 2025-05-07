/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.TupleSet

open Lean

/- e.g.
@[default_instance]
instance : rel_test_fs.vars ThoR_TupleSet := by sorry
-/

macro "create_default_block_vars_tuple_set" blockName:ident : command
  => do
    let varName ← `($(mkIdent s!"{blockName.getId}.vars".toName))
    `(
      @[default_instance]
      instance : $varName $(mkIdent `ThoR_TupleSet) := by sorry
    )
