/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.Set

open Lean PrettyPrinter Delaborator SubExpr Expr
open ThoR

@[app_unexpander And]
def unexpandAnd : Unexpander
  | `($_ $a $b) => `($a $(mkIdent `and) $b)
  | _ => throw Unit.unit

@[app_unexpander Or]
def unexpandOr : Unexpander
  | `($_ $a $b) => `($a $(mkIdent `or) $b)
  | _ => throw Unit.unit

@[app_unexpander Iff]
def unexpandIff : Unexpander
  | `($_ $a $b) => `($a $(mkIdent `iff) $b)
  | _ => throw Unit.unit
