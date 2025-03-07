/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Constant.constant
import ThoR.Shared.Syntax.Constant.constantSyntax

import ThoR.Alloy.Config
import ThoR.Relation.Rel

open ThoR Config Lean

namespace Shared.constant

  /--
  Generates a string representation of the type
  -/
  def toString (c : constant) : String := s!"{c}"

  /--
  Generates syntax corosponding to the type
  -/
  def toSyntax (c : constant) : TSyntax `constant := Unhygienic.run do
    match c with
      | constant.none => `(constant| none)
      | constant.iden => `(constant| iden)
      | constant.univ => `(constant| univ)

  /--
  Generates a Lean term corosponding with the type
  -/
  def toTerm
    (c : constant)
    : TSyntax `term := Unhygienic.run do
      match c with
        | constant.none =>
          `($(mkIdent ``Rel.constant.none) $(baseType.ident))
        | constant.univ =>
          `($(mkIdent ``Rel.constant.univ) $(baseType.ident))
        | constant.iden =>
          `($(mkIdent ``Rel.constant.iden) $(baseType.ident))

  /--
  Parses the given syntax to the type
  -/
  def toType (c : TSyntax `constant) : constant :=
    match c with
      | `(constant| none) => constant.none
      | `(constant| iden) => constant.iden
      | `(constant| univ) => constant.univ

      | _ => constant.none -- unreachable

end Shared.constant
