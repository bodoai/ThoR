/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
open Lean

namespace Alloy

  declare_syntax_cat extendedIdent
  syntax ident : extendedIdent
  syntax "def" : extendedIdent
  syntax "alloy" : extendedIdent

  namespace extendedIdent

    def toName (ei: TSyntax `extendedIdent) : Name :=
      match ei with
        | `(extendedIdent| $i:ident) => i.getId
        | `(extendedIdent| def) => `def
        | `(extendedIdent| alloy) => `alloy
        | _ => default

  end extendedIdent

end Alloy
