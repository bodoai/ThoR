/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean

open Lean PrettyPrinter Delaborator SubExpr Expr

@[app_unexpander Add.add]
def unexpandAdd : Unexpander
  | `($_ $a $b) =>
    `($(mkIdent `plus) [$a, $b])

  | _ => throw Unit.unit

@[app_unexpander Sub.sub]
def unexpandSub : Unexpander
  | `($_ $a $b) =>
    `($(mkIdent `minus) [$a, $b])

  | _ => throw Unit.unit

@[app_unexpander Mul.mul]
def unexpandMul : Unexpander
  | `($_ $a $b) =>
    `($(mkIdent `mul) [$a, $b])

  | _ => throw Unit.unit

@[app_unexpander Div.div]
def unexpandDiv : Unexpander
  | `($_ $a $b) =>
    `($(mkIdent `div) [$a, $b])

  | _ => throw Unit.unit

@[app_unexpander Mod.mod]
def unexpandMod : Unexpander
  | `($_ $a $b) =>
    `($(mkIdent `rem) [$a, $b])

  | _ => throw Unit.unit
