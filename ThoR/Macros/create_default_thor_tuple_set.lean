/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.TupleSet

open Lean

/-
-- maybe better to not do it as macro but rather import it as follows?
@[default_instance]
instance : ThoR.TupleSet ThoR_TupleSet := by sorry
-/

macro "create_default_thor_tuple_set" : command
  => do
    `(
      @[default_instance]
      instance : $(mkIdent ``ThoR.TupleSet) $(mkIdent `ThoR_TupleSet) := by sorry
    )
