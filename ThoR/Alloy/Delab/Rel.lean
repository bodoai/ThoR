/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.Notation
import ThoR.Relation.Elab
import ThoR.Alloy.Delab.DelaborationService

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander ThoR.Rel.relation]
def unexpTypedRelToRel : Unexpander
  | `($_ $_ $_ $_ $r) => `($r)
  | _ => throw Unit.unit

-- FIXME
@[app_unexpander ThoR.Rel.getType]
def unexpTypedRelGetType : Unexpander
  | `($_ $r) => `($r)
  | _ => throw Unit.unit

@[app_unexpander ThoR.Rel]
def unexpTypedRel : Unexpander
  | `($_ $t:ident) =>
    let new_t :=
      delaborationService.switch_thoR_representation_to_alloy_representation t
    `($new_t)
  | `($_ $t) => `($t)
  | _ => throw Unit.unit

@[app_unexpander ThoR.Rel.constant.univ]
def unexpTypedRelConstantUniv : Unexpander
  | `($_ $_) => `($(mkIdent `univ))
  | _ => throw Unit.unit

@[app_unexpander ThoR.Rel.constant.none]
def unexpTypedRelConstantNone : Unexpander
  | `($_ $_) => `($(mkIdent `none))
  | _ => throw Unit.unit

@[app_unexpander ThoR.Rel.constant.iden]
def unexpTypedRelConstantIden : Unexpander
  | `($_ $_) => `($(mkIdent `iden))
  | _ => throw Unit.unit
