/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.Formula.formula

open Shared

open Lean
namespace Alloy

  /-- Type representation of a property.
      A property is in fact 'just' the body of an assert or fact declaration.
  -/
  structure property where
    mk :: (name : String)
          (formulas : List (formula))
  deriving Repr, Inhabited

  /-- Syntax representation of a property -/
  declare_syntax_cat property
  abbrev Property := TSyntax `property
  syntax "{"
    formula*
  "}" : property

  instance : ToString property where
    toString (p : property) : String :=
      s!"\{
            name := {p.name},
            formulas := {p.formulas}
          }"

  /-- Generates a String representation of a property -/
  def property.toString (p : property) : String := ToString.toString p

end Alloy
