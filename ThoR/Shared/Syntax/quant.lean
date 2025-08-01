/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Alloy.Exceptions.NoMatchImplementedException

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
  abbrev Quant := TSyntax `quant
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
    def toType
      (q: Quant)
      : Except String quant := do
        match q with
          | `(quant| all) => return quant.all
          | `(quant| some) => return quant.some
          | `(quant| lone) => return quant.lone
          | `(quant| one) => return quant.one
          | `(quant| no) => return quant.no

          | syntx =>
            throwNoMatchImplemented "quant.toType" syntx

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (q: quant) : Term := Unhygienic.run do
      match q with
        | quant.all => `($(mkIdent ``quant.all))
        | quant.some => `($(mkIdent ``quant.some))
        | quant.lone => `($(mkIdent ``quant.lone))
        | quant.one => `($(mkIdent ``quant.one))
        | quant.no => `($(mkIdent ``quant.no))

    /--
    Generates syntax corosponding to the type
    -/
    def toSyntax (q: quant) : Quant := Unhygienic.run do
      match q with
        | quant.all => `(quant | all)
        | quant.some => `(quant | some)
        | quant.lone => `(quant | lone)
        | quant.one => `(quant | one)
        | quant.no => `(quant | no)

  end quant

end Shared
