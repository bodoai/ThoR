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
    def toString
      (pa: predArg)
      (inner_space_count := 3)
      (outer_space_count := 1)
      (leading_new_line := false)
      : String := Id.run do

      let mut inner_spaces : String := ""
      for _ in [0:inner_space_count] do
        inner_spaces := inner_spaces ++ " "

      let mut outer_spaces : String := ""
      for _ in [0:outer_space_count] do
        outer_spaces := outer_spaces ++ " "

      let result :=
        outer_spaces ++ "predicate argument : ⦃" ++ "\n" ++
        inner_spaces ++ s!"names := {pa.names}," ++ "\n" ++
        inner_spaces ++ s!"disjunction := {pa.disjunction}," ++ "\n" ++
        inner_spaces ++ s!"expression := {pa.expression}" ++ "\n" ++
        outer_spaces ++ "⦄"

      if leading_new_line then
        "\n" ++ result
      else
        result

    instance : ToString predArg where
    toString (pa : predArg) : String := pa.toString

  end predArg

end Alloy
