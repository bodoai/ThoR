/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

import ThoR.Alloy.Syntax.Predicate.PredArg.predArg
import ThoR.Alloy.Syntax.Predicate.PredArg.predArgService

import ThoR.Shared.Syntax.Formula.formula
import ThoR.Shared.Syntax.Formula.formulaService

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

    /--
    Creates a predicate declaration with arguments
    -/
    def createWithArgs
      (name : Name)
      (args : Syntax.TSepArray `predArg ",")
      (forms : TSyntaxArray `formula)
      : predDecl := Id.run do

      let args : List (predArg) :=
        (args.getElems.map fun (arg) => (predArg.toType arg)).toList

      let forms : List (formula) :=
        (forms.map fun (f) => (formula.toType f)).toList

      {
        name := name.toString
        args := args
        forms := forms
      }

    /--
    Creates a predicate declaration without arguments
    -/
    def createWithoutArgs
      (name : Name)
      (forms : TSyntaxArray `formula)
      : predDecl := Id.run do

      let forms : List (formula) :=
        (forms.map fun (f) => (formula.toType f)).toList

      {
        name := name.toString
        args := []
        forms := forms
      }

    /--
    Parses te given syntax to a structure of predDecl if possible
    -/
    def toType (pd : TSyntax `predDecl) : predDecl :=
      match pd with
        -- pred declaration with args
        | `(predDecl| pred $name:extendedIdent ($args:predArg,*) {
            $forms:formula*
          }) =>
            predDecl.createWithArgs (extendedIdent.toName name) args forms

        | `(predDecl| pred $name:extendedIdent [$args:predArg,*] {
            $forms:formula*
          }) =>
            predDecl.createWithArgs (extendedIdent.toName name) args forms

        -- pred declaration without args
        | `(predDecl| pred $name:extendedIdent {
            $forms:formula*
          }) =>
            predDecl.createWithoutArgs (extendedIdent.toName name) forms

        | _ => {name := "PANIC!", args := [], forms := []}

    /--
    Gets the required definitions for the predicate declaration to work
    -/
    def getReqDefinitions
      (pd : predDecl)
      : List (String) := Id.run do
        let mut result : List (String) := []

        for form in pd.forms do
          result := result ++ form.getReqDefinitions

        return result

    /--
    Gets the required variables for the predicate declaration to work
    -/
    def getReqVariables
      (pd : predDecl)
      : List (String) := Id.run do
        let mut result : List (String) := []

        for arg in pd.args do
          result := result ++ arg.expression.getReqVariables

        for form in pd.forms do
          result := result ++ form.getReqVariables

        return result

  end predDecl

end Alloy
