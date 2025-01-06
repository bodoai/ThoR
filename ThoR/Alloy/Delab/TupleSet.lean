/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean

import ThoR.Relation.TupleSet
import ThoR.Relation.Elab

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander ThoR.RelConstants.univ]
def unexpRelConstantsUniv : Unexpander
  | `($_) => pure $ mkIdent `univ
