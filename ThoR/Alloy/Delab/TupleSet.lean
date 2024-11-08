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
  | `($_ $a $b) => `($a . $b)
  | _ => throw Unit.unit
