/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean

open Lean Lean.Elab Term

namespace Alloy

  declare_syntax_cat delaborator_body
  syntax term : delaborator_body
  syntax term "+" term : delaborator_body
  syntax term "=" term : delaborator_body
  syntax "{" term "}" : delaborator_body

  instance : Coe (TSyntax `delaborator_body) Term  where
  coe s := ⟨s.raw⟩

  syntax
    (name := delaboration_alloy_syntax)
    "[" "alloy'" "|"
      delaborator_body
    "]"
    : term

  @[term_elab delaboration_alloy_syntax]
  private def alloyFormulaBlockImpl : TermElab := fun _ _ => do
    throwError s!"This syntax is used only for delaboration. Use blockless \
    alloy (e.g. [alloy | forumla*]) instead."

end Alloy
