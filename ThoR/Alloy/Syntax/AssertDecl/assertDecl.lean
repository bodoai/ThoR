/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Alloy.Syntax.Property.property

import ThoR.Alloy.Syntax.SeparatedNamespace.extendedIdent

open Lean
open Shared

namespace Alloy

  /--
  A type representation of an assert declaration. It is projected on `property`
  -/
  def assertDecl := property
  deriving Repr

  -- would be prettier to call the default of property
  instance : Inhabited assertDecl where
    default := {name := "Empty", formulas := []}

  /--
  A syntax repreaentation of an assert declaration.
  -/
  declare_syntax_cat assertDecl
  abbrev AssertDecl := TSyntax `assertDecl
  syntax "assert " extendedIdent property : assertDecl

  instance : ToString assertDecl where
    toString (ad : assertDecl) : String :=
      s!"assert : {property.toString ad}"

  /-- Generates a String representation from the type -/
  def assertDecl.toString (ad : assertDecl) : String := ToString.toString ad

end Alloy
