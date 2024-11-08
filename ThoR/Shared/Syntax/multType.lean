/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
Had to be separated from mult.Lean in order to be
able to use the definition of this inductive datatype
and in the same file define an instance
of the typeclass SetMultPredicates.
-/
import ThoR.Basic

namespace Shared

  /--
  This inductive type represents an alloy multiplicity
  -/
  inductive mult
    | set
    | some
    | lone
    | one
  deriving Repr

end Shared
