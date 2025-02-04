/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

open Lean

namespace Shared

  /--
  This inductive type represents an alloy quantifier
  -/
  inductive quant
    | all
    | some
    | lone
    | one
    | no
  deriving Repr, BEq

  /--
  This syntax represents an alloy quantifier
  -/
  declare_syntax_cat quant
  syntax "all" : quant
  syntax "some" : quant
  syntax "lone" : quant
  syntax "one" : quant
  syntax "no" : quant

  instance : ToString quant where
    toString : quant -> String
      | quant.all => "all"
      | quant.some => "some"
      | quant.lone => "lone"
      | quant.one => "one"
      | quant.no => "no"
  namespace quant

    /--
    Generates a string representation of the type
    -/
    def toString (q : quant) : String := ToString.toString q

    /--
    Parses the given syntax to the type
    -/
    def toType (q: TSyntax `quant) : quant :=
      match q with
        | `(quant| all) => quant.all
        | `(quant| some) => quant.some
        | `(quant| lone) => quant.lone
        | `(quant| one) => quant.one
        | `(quant| no) => quant.no

        | _ => quant.all -- unreachable

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (q: quant) : TSyntax `term := Unhygienic.run do
      match q with
        | quant.all => `($(mkIdent ``quant.all))
        | quant.some => `($(mkIdent ``quant.some))
        | quant.lone => `($(mkIdent ``quant.lone))
        | quant.one => `($(mkIdent ``quant.one))
        | quant.no => `($(mkIdent ``quant.no))

    /--
    Generates syntax corosponding to the type
    -/
    def toSyntax (q: quant) : TSyntax `quant := Unhygienic.run do
      match q with
        | quant.all => `(quant | all)
        | quant.some => `(quant | some)
        | quant.lone => `(quant | lone)
        | quant.one => `(quant | one)
        | quant.no => `(quant | no)

  end quant

end Shared
