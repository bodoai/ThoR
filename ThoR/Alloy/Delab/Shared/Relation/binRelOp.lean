/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.Set
import ThoR.Shared.Syntax.Relation.relationSeparator

open Lean PrettyPrinter Delaborator SubExpr Expr

-- TODO In welchem Namespace sollen die ThoR-spezifischen
--      Typklassen definiert werden?
--      - root
--      - ThoR
--      Nach getroffener Entscheidung: einheitlich handhaben.
@[app_unexpander ThoR.Dotjoin.dotjoin]
def unexpDotjoin : Unexpander
  | `($_ $a $b) => `($a . $b)
  | _ => throw Unit.unit

@[app_unexpander ThoR.HDotjoin.hDotjoin]
def unexpHDotjoin : Unexpander
  | `($_ $a:ident $b:ident) => do

    let new_a := mkIdent (a.getId.updateLast fun s =>
      let split := s.splitOn relationSeparator.get
      if split.length > 1 then split.getLast! else s
    )

    let new_b := mkIdent (b.getId.updateLast fun s =>
      let split := s.splitOn relationSeparator.get
      if split.length > 1 then split.getLast! else s
    )

    `($new_a . $new_b)

  | _ => throw Unit.unit
