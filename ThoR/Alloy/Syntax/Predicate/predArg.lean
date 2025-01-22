/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.Relation.Expr.expr
import ThoR.Shared.Syntax.Relation.Expr.exprService

open Shared Lean

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

  namespace predArg

    /--
    Generates a string representation of the structure
    -/
    def toString (pa: predArg) : String := ToString.toString pa

    /--
    Creates a predicate argument from the given parameters
    -/
    def create
      (disjunction:Bool)
      (names: Syntax.TSepArray `ident ",")
      (e: TSyntax `expr)
      : predArg := Id.run do

      let names := (names.getElems.map fun (elem) => elem.getId.lastComponentAsString).toList
      let e := (expr.toType e)

      return {
        disjunction := disjunction
        names:= names
        expression := e
      }

    /--
    Parses the given syntax to a predArg if possible
    -/
    def toType (arg : TSyntax `predArg) : predArg :=
      match arg with
        | `(predArg| disj $names:ident,* : $expression:expr) =>
          create true names expression

        | `(predArg| $names:ident,* : $expression:expr) =>
          create False names expression

        | _ => {
            disjunction := false
            expression := expr.const constant.none
            names:= ["panic"]
          } -- unreachable

    end predArg

end Alloy
