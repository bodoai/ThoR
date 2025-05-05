/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Shared.Syntax.multType
open Lean
namespace Shared

  -- Type is to be found in multType

  /--
  This syntax represents an alloy multiplicity
  -/
  declare_syntax_cat mult
  abbrev Mult := TSyntax `mult
  syntax "some" : mult
  syntax "one" : mult
  syntax "lone" : mult
  syntax "set" : mult -- ist in Alloy nicht in syntax cat. mult definiert

  namespace mult

    instance : ToString mult where
      toString : mult -> String
        | mult.one => "one"
        | mult.set => "set"
        | mult.some => "some"
        | mult.lone => "lone"

    /--
    Generates a string representation of the type
    -/
    def toString (m : mult) : String := s!"{m}"

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (m : mult) : Term := Unhygienic.run do
      match m with
        | mult.one => `($(mkIdent ``mult.one))
        | mult.set => `($(mkIdent ``mult.set))
        | mult.some => `($(mkIdent ``mult.some))
        | mult.lone => `($(mkIdent ``mult.lone))

    /--
    Generates syntax corosponding to the type
    -/
    def toSyntax (m : mult) : Mult := Unhygienic.run do
      match m with
        | mult.one => `(mult| one)
        | mult.set => `(mult| set)
        | mult.some => `(mult| some)
        | mult.lone => `(mult| lone)

    /--
    Parses the given syntax to the type
    -/
    def toType
      (m : Mult)
      : Except String mult := do
        match m with
          | `(mult| set) => return mult.set
          | `(mult| some) => return mult.some
          | `(mult| lone) => return mult.lone
          | `(mult| one) => return mult.one

          | syntx => throw s!"No match implemented in \
            mult.toType \
            for '{syntx}'"

    /--
    Tries to parse an mult from an option syntax and
    returns the set mult if no mult is to be found
    -/
    def fromOption
      (m : Option Mult)
      : Except String mult :=
      match m with
        | Option.some mul => return ← mult.toType mul
        | Option.none => return mult.set

  end mult

end Shared
