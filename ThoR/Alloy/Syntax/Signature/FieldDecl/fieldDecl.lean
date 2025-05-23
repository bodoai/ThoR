/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Shared.Syntax.TypeExpr.typeExpr

import ThoR.Alloy.Syntax.SeparatedNamespace.extendedIdent

open Shared

namespace Alloy

  /--
  This structure represents a field in a Alloy signature
  -/
  structure fieldDecl where
    mk :: (names : List (String)) -- min 1
          (type : typeExpr)
  deriving Repr

  /--
  This syntax represents a field in a Alloy signature
  -/
  declare_syntax_cat fieldDecl
  syntax extendedIdent,+ " : " typeExpr : fieldDecl

  instance : ToString fieldDecl where
    toString (fd : fieldDecl) : String :=
      s!"fieldDecl :\{
            names := {fd.names},
            type := {fd.type}
          }"

  /--
  Generates a String representation from the structure
  -/
  def fieldDecl.toString (fd : fieldDecl) : String := ToString.toString fd

end Alloy
