/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.Elab
import ThoR.Alloy.Delab.DelaborationAlloySyntax
import ThoR.Alloy.Delab.DelaborationService

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander ThoR.RelType.unary_rel]
def unexpRelTypeConsSimple : Unexpander
  | `($_ $m $s:ident) =>
    let new_s :=
      delaborationService.switch_thoR_representation_to_alloy_representation s
    `($m [alloy' | $new_s.toSyntax])

  | _ => throw Unit.unit

@[app_unexpander ThoR.RelType.complex]
def unexpRelTypeConsComplexRel : Unexpander
  | `($_ $e1 $m1 $m2 $e2) =>
    `(term | $e1 $m1 → $m2 $e2)

  | _ => throw Unit.unit

@[app_unexpander ThoR.RelType.mk.unary_rel]
def unexpRelTypeMkUnaryRel : Unexpander
  | `($_ $m $r:ident) =>
    let new_r :=
      delaborationService.switch_thoR_representation_to_alloy_representation r
    `($m [alloy' | $new_r.toSyntax])

  | `($_ $m $r) =>  `($m $r)

  | _ => throw Unit.unit

@[app_unexpander ThoR.RelType.mk.rel]
def unexpRelTypeMkRel : Unexpander
  | `($_ $r:ident) =>
    let new_r :=
      delaborationService.switch_thoR_representation_to_alloy_representation r
    `([alloy' | $new_r.toSyntax] )
  | `($_ $r) => `($r)
  | _ => throw Unit.unit
