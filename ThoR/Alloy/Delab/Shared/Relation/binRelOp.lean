/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.Set
import ThoR.Alloy.Delab.DelaborationService

open Lean PrettyPrinter Delaborator SubExpr Expr

-- TODO In welchem Namespace sollen die ThoR-spezifischen
--      Typklassen definiert werden?
--      - root
--      - ThoR
--      Nach getroffener Entscheidung: einheitlich handhaben.
set_option linter.cdot false in
@[app_unexpander ThoR.Dotjoin.dotjoin]
def unexpDotjoin : Unexpander
  | `($_ $a $b) => `($a . $b)
  | _ => throw Unit.unit

set_option linter.cdot false in
@[app_unexpander ThoR.HDotjoin.hDotjoin]
def unexpHDotjoin : Unexpander
  | `($_ $a:ident $b:ident) => do

    let new_a :=
      delaborationService.switch_thoR_representation_to_alloy_representation a
    let new_b :=
      delaborationService.switch_thoR_representation_to_alloy_representation b

    `($new_a . $new_b)

  | _ => throw Unit.unit
