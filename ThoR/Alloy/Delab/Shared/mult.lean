/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.Elab
import ThoR.Shared.Syntax.mult

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander Shared.mult.set]
def unexpSharedMultSet : Unexpander
  | `($_) => pure $ mkIdent `set

@[app_unexpander Shared.mult.lone]
def unexpSharedMultLone : Unexpander
  | `($_) => pure $ mkIdent `lone

@[app_unexpander Shared.mult.one]
def unexpSharedMultOne : Unexpander
  | `($_) => pure $ mkIdent `one

@[app_unexpander Shared.mult.some]
def unexpSharedMultSome : Unexpander
  | `($_) => pure $ mkIdent `some
