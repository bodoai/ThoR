/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.formula

open Shared

open Lean
namespace Alloy

  /-- Type representation of a property.
      A property is in fact 'just' the body of an assert or fact declaration.
  -/
  structure property where
    mk :: (name : String)
          (formulas : List (formula))
  deriving Repr

  /-- Syntax representation of a property -/
  declare_syntax_cat property
  syntax "{"
    formula*
  "}" : property

  instance : ToString property where
    toString (p : property) : String :=
      s!"\{
            name := {p.name},
            formulas := {p.formulas}
          }"

  namespace property

    /-- Generates a String representation of a property -/
    def toString (p : property) : String := ToString.toString p

    /-- Default value of a property (empty). -/
    instance : Inhabited property where
      default := {name := "Empty", formulas := []}

    /-- Creates a property from a name and formulas -/
    private def create
      (name : TSyntax `ident)
      (formulas : TSyntaxArray `formula)
      : property := Id.run do

      let formulas : List (formula) :=
        (formulas.map fun (f) => (formula.toType f)).toList

      {
        name:= name.getId.lastComponentAsString,
        formulas := formulas
      }

    /-- Creates a type representation from syntax and a name-/
    def toType
      (name: TSyntax `ident)
      (p:TSyntax `property)
      : property :=
      match p with
        | `(property | { $formulas:formula*}) =>
          create name formulas
        | _ => default

  end property

end Alloy