/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.Notation

open Lean PrettyPrinter Delaborator SubExpr Expr

@[app_unexpander Neg.neg]
def unexpandNeg : Unexpander
  | `($_ $a) =>
    `(- $a)

  | _ => throw Unit.unit

@[app_unexpander ThoR.Card.card]
def unexpandCard : Unexpander
  | `($_ $a) =>
    `(#$a)

  | `($_) => `($(mkIdent `card)) -- correct?

  --| _ => throw Unit.unit
