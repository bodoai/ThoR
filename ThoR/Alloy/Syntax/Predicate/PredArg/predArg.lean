/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.Relation.Expr.expr

open Shared
open Lean
namespace Alloy

  /--
  This strucutre represents a predicate argument
  -/
  structure predArg where
    mk :: (disjunction: Bool)
          (names: List (String))
          (expression : expr)
  deriving Repr

  /--
  This syntax represents a predicate argument
  -/
  declare_syntax_cat predArg
  abbrev PredArg := TSyntax `predArg
  syntax ("disj")? ident,+ ":" expr : predArg

  instance : ToString predArg where
    toString (pa : predArg) : String :=
      s!"predicateArgument : \{
          names := {pa.names},
          disjunction := {pa.disjunction},
          expression := {pa.expression}
        }"

  instance : Inhabited predArg where
    default := {
        disjunction := false
        names:= ["default"]
        expression := expr.const (constant.none)
      }

  instance : BEq predArg where
    beq (predArg1 predArg2 : predArg) :=
      predArg1.names == predArg2.names &&
      predArg1.disjunction == predArg2.disjunction &&
      predArg1.expression == predArg2.expression

  namespace predArg

    /--
    Generates a string representation of the structure
    -/
    def toString (pa: predArg) : String := ToString.toString pa

  end predArg

end Alloy
