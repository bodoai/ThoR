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
    def toTerm (m : mult) : TSyntax `term := Unhygienic.run do
      match m with
        | mult.one => `($(mkIdent ``mult.one))
        | mult.set => `($(mkIdent ``mult.set))
        | mult.some => `($(mkIdent ``mult.some))
        | mult.lone => `($(mkIdent ``mult.lone))

    instance : BEq mult where
      beq : mult -> mult -> Bool
        | m1, m2 => m1.toString == m2.toString

    /--
    Generates syntax corosponding to the type
    -/
    def toSyntax (m : mult) : TSyntax `mult := Unhygienic.run do
      match m with
        | mult.one => `(mult| one)
        | mult.set => `(mult| set)
        | mult.some => `(mult| some)
        | mult.lone => `(mult| lone)

    /--
    Parses the given syntax to the type
    -/
    def toType (m : TSyntax `mult) : mult :=
      match m with
        | `(mult| set) => mult.set
        | `(mult| some) => mult.some
        | `(mult| lone) => mult.lone
        | `(mult| one) => mult.one

        | _ => mult.one -- unreachable

    /--
    Tries to parse an mult from an option syntax and
    returns the set mult if no mult is to be found
    -/
    def fromOption (m : Option (TSyntax `mult)) : mult :=
      match m with
        | Option.some mul => mult.toType mul
        | Option.none => mult.set

  end mult

end Shared