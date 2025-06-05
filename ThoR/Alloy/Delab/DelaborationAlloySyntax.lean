/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean

open Lean Lean.Elab Term

namespace Alloy

  declare_syntax_cat delaborator_body
  syntax ident : delaborator_body

  /-unaryRelOperation-/
  /--transposition-/
  syntax "~" delaborator_body : delaborator_body
  /--transitive_closure-/
  syntax "^" delaborator_body : delaborator_body
  /--reflexive_closure-/
  syntax "*" delaborator_body : delaborator_body

  /-binaryRelOperation-/
  /--intersection-/
  syntax delaborator_body "&" delaborator_body : delaborator_body
  /--union-/
  syntax delaborator_body "+" delaborator_body : delaborator_body
  /--difference-/
  syntax delaborator_body "-" delaborator_body : delaborator_body
  /--overwrite-/
  syntax delaborator_body "++" delaborator_body : delaborator_body
  /--domain_restriction-/
  syntax delaborator_body "<:" delaborator_body : delaborator_body
  /--range_restriction-/
  syntax delaborator_body ":>" delaborator_body : delaborator_body

  /-dotjoin-/
  syntax delaborator_body "." delaborator_body : delaborator_body

  /-rel_if_else-/
  syntax delaborator_body "=>" delaborator_body "else" delaborator_body : delaborator_body

  /-unRelBoolOp-/
  /--no-/
  syntax "no" delaborator_body : delaborator_body
  /--one-/
  syntax "one" delaborator_body : delaborator_body
  /--lone-/
  syntax "lone" delaborator_body : delaborator_body
  /--none-/
  syntax "none" delaborator_body : delaborator_body

  /--not-/
  syntax "none" delaborator_body : delaborator_body

  /--relCompareOperation-/
  syntax delaborator_body "=" delaborator_body : delaborator_body


  syntax "pred" ident delaborator_body+ : delaborator_body
  syntax "[" delaborator_body,+ "]" : delaborator_body
  syntax "{" delaborator_body "}" : delaborator_body

  instance : Coe (TSyntax `delaborator_body) Ident where
  coe s := ⟨s.raw⟩

  instance : Coe Ident (TSyntax `delaborator_body) where
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
