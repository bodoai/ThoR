/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.Elab

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander ThoR.SetMultPredicates.no]
def unexpSetPredicatesNo : Unexpander
  | `($_ $param) => `($(mkIdent `no) $param)
  | _ => throw Unit.unit
@[app_unexpander ThoR.SetMultPredicates.lone]
def unexpSetPredicatesLone : Unexpander
  | `($_ $param) => `($(mkIdent `lone) $param)
  | _ => throw Unit.unit
@[app_unexpander ThoR.SetMultPredicates.one]
def unexpSetPredicatesOne : Unexpander
  | `($_ $param) => `($(mkIdent `one) $param)
  | _ => throw Unit.unit
@[app_unexpander ThoR.SetMultPredicates.some]
def unexpSetPredicatesSome : Unexpander
  | `($_ $param) => `($(mkIdent `some) $param)
  | _ => throw Unit.unit
