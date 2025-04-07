/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/-
This file defines the Syntax fpr module variables and how to get their ident
-/

import Lean
open Lean

namespace Alloy

  declare_syntax_cat moduleVar
  syntax ("exactly")? ident : moduleVar
  abbrev ModuleVar := Lean.TSyntax `moduleVar

  def moduleVar.getIdent
    (mv : ModuleVar)
    : Ident :=
      match mv with
        | `(moduleVar | exactly $i:ident) => i
        | `(moduleVar | $i:ident) => i
        | _ => unreachable!

end Alloy
