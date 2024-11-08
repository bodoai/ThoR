/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean

open Lean PrettyPrinter Delaborator SubExpr Expr

@[app_unexpander Not]
def unexpandNot : Unexpander
  | `($_ $a) => `($(mkIdent `not) ($a))
  | _ => throw Unit.unit
