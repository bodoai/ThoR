/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
open Lean

namespace Shared

  /--
    Removes the unhygienic monad from a syntax
  -/
  def unhygienicUnfolder
    {type : Type}
    (input : Unhygienic (type))
    : type := Unhygienic.run do
    return ← input

end Shared
