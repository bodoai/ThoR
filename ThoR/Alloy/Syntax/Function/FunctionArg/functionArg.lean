/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Shared.Syntax.TypeExpr.typeExpr

open Shared
open Lean

namespace Alloy

  /--
  This structure represents a function argument
  -/
  structure functionArg where
    mk :: (disjunction: Bool)
          (names: List (String))
          (type : typeExpr)
  deriving Repr, BEq

  /--
  This syntax represents a function argument
  -/
  declare_syntax_cat functionArg
  syntax ("disj")? ident,+ ":" typeExpr : functionArg

  abbrev FunctionArg := TSyntax `functionArg

  instance : ToString functionArg where
    toString (fa : functionArg) : String :=
      s!"function argument : \{
          names := {fa.names},
          disjunction := {fa.disjunction},
          type := {fa.type}
        }"

  instance : Inhabited functionArg where
    default := {
        disjunction := false
        names:= ["default"]
        type := default
      }

  namespace functionArg

    /--
    Generates a string representation of the structure
    -/
    def toString (fa: functionArg) : String := ToString.toString fa

  end functionArg

end Alloy
