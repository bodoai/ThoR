/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean

open Lean

def throwNoMatchImplemented
  {α : Type}
  (place : String)
  (syntx : Syntax)
  : Except String α :=
    throw s!"No match implemented in {place} for '{syntx}'"
