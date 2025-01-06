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
  | `($_ $a $b:ident) => do
    let bn :=
      mkIdent
        (b.getId.updateLast
          fun lc =>
            let lcSplit := lc.splitOn relationSeparator.get
            if lcSplit.length > 1 then
              let last := lcSplit.getLast!
              last
            else
              lc
        )

    `($a . $bn)
  | _ => throw Unit.unit
