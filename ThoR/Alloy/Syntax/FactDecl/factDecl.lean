/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

import ThoR.Alloy.Syntax.AssertDecl.assertDecl

import ThoR.Alloy.Syntax.SeparatedNamespace.extendedIdent

open Lean

namespace Alloy

  /--
  A type representation of an fact declaration. It is projected on `property`
  -/
  def factDecl := property
  deriving Repr, Inhabited

  /--
  A syntax repreaentation of an fact declaration.
  -/
  declare_syntax_cat factDecl
  abbrev FactDecl := TSyntax `factDecl
  syntax "fact " (extendedIdent)? property : factDecl

  instance : ToString factDecl where
    toString (fd : factDecl) : String :=
      s!"fact : {property.toString fd}"

  /-- Generates a String representation from the type -/
  def factDecl.toString (fd : factDecl) : String := ToString.toString fd

end Alloy
