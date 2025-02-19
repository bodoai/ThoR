/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

import ThoR.Alloy.Syntax.Predicate.PredArg.predArg

import ThoR.Shared.Syntax.Formula.formula

import ThoR.Alloy.Syntax.SeparatedNamespace.extendedIdent

open Lean
open Shared

namespace Alloy

  /--
  This structure represents an Alloy predicate declaration
  -/
  structure predDecl where
    mk :: (name : String)
          (args : List (predArg))
          (forms : List (formula))
  deriving Repr, BEq

  /--
  This syntax represents an Alloy predicate declaration
  -/
  declare_syntax_cat predDecl
  syntax "pred " extendedIdent ("("predArg,*")")? "{"
    formula*
  "}": predDecl
  syntax "pred " extendedIdent ("["predArg,*"]")? "{"
    formula*
  "}": predDecl

  namespace predDecl

    instance : ToString predDecl where
    toString (pd : predDecl) : String :=
      s!"predicate : \{
            name := {pd.name},
            arguments := {pd.args},
            formulas := {pd.forms}
          }"

    instance : Inhabited predDecl where
      default := {
          name := ""
          args := []
          forms := []
        }

    /--
    Generates a string representation of the structure
    -/
    def toString (pd : predDecl) : String := ToString.toString pd

    /--
    Adds a single argument (predArg) to the prediacte declaration
    -/
    def addPredArg (pd : predDecl) (pa : predArg) : predDecl :=
      {pd with args := pd.args.append [pa]}

  end predDecl

end Alloy
