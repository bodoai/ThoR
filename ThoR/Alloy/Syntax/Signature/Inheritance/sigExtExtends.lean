/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

import ThoR.Shared.Syntax.TypeExpr.typeExpr

open Shared Lean

namespace Alloy

  /--
  This strucutre represents an 'extends' extension of a Alloy signature declaration
  -/
  structure sigExtExtends where
    mk :: (type : typeExpr)
  deriving Repr

  /--
  This syntax represents an 'extends' extension of a Alloy signature declaration
  -/
  declare_syntax_cat sigExtExtends
  syntax (" extends " ident) : sigExtExtends

  instance : ToString sigExtExtends where
    toString (see : sigExtExtends) : String :=
      s!"extends {see.type.toString}"
  namespace sigExtExtends

    /--
    Generates a string representation of the structure
    -/
    def toString (see : sigExtExtends) : String := ToString.toString see

    /--
    Creates an empty extension strucutre with the given name.
    -/
    def create (name : TSyntax `ident) : sigExtExtends :=
        {type:=
          (typeExpr.multExpr mult.set
            (expr.string name.getId.lastComponentAsString)
          )
        }

  end sigExtExtends

end Alloy
