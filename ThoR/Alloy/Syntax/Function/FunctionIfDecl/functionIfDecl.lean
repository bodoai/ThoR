/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Formula.formula

open Lean
open Shared

namespace Alloy

  /--
  This represents an if declaration inside a function.
  This is necessary since the if can be a formula and
  can thus not be defined in expr. (Alternative: Create
  a bool expr, which can be used as condition instead?)
  -/
  structure functionIfDecl where
    (condition : formula)
    (thenBody : expr)
    (elseBody : expr)
    (hasElse : Bool)
  deriving Repr, BEq, Inhabited

  declare_syntax_cat functionIfDecl
  abbrev FunctionIfDecl:= TSyntax `functionIfDecl
  syntax "(" functionIfDecl ")" : functionIfDecl

  declare_syntax_cat connector
  syntax "=>" : connector

  declare_syntax_cat ifbody
  syntax connector:60 expr ("else" expr)? : ifbody

  syntax:60 formula_without_if:70 ifbody:60 : functionIfDecl
  syntax:50 "(" formula:70 ")" ifbody:60 : functionIfDecl

  instance : ToString functionIfDecl where
    toString (fid : functionIfDecl) : String :=
      s!"(function) if declaration : \{
        condition := {fid.condition},
        thenBody := {fid.thenBody},
        {
          if fid.hasElse then
            s!"elseBody := {fid.elseBody}"
          else ""
        }
      }"

end Alloy
