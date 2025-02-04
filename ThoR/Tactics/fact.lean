/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Relation.ElabCallMacro

/--
Declares a new fact with the given name, refering to one created from
an alloy block.

Defined like "fact `new_name` : `refered_name`"
-/
macro "fact" new_name:ident ":" refered_name:ident : tactic =>
  `(tactic| have $new_name := ∻ $refered_name)
