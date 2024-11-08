/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Relation.Elab

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander ThoR.RelType.unary_rel]
def unexpRelTypeConsSimple : Unexpander
  | `($_ $m $s) => `($m $s)
  | _ => throw Unit.unit

@[app_unexpander ThoR.RelType.complex]
def unexpRelTypeConsComplexRel : Unexpander
  | `($_ $e1 $m1 $m2 $e2) => `($e1 $m1 → $m2 $e2)
  | _ => throw Unit.unit

@[app_unexpander ThoR.RelType.mk.unary_rel]
def unexpRelTypeMkUnaryRel : Unexpander
  | `($_ $m $r) => `($m $r)
  | _ => throw Unit.unit

@[app_unexpander ThoR.RelType.mk.rel]
def unexpRelTypeMkRel : Unexpander
  | `($_ $r) => `($r)
  | _ => throw Unit.unit
