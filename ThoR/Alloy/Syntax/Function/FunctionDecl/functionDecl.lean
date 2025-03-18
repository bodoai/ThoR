/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Alloy.Syntax.Function.FunctionArg.functionArg
import ThoR.Alloy.Syntax.SeparatedNamespace.extendedIdent

open Lean
open Shared

namespace Alloy

  /--
  This structure represents an Alloy function declaration
  -/
  structure functionDecl where
    mk :: (name : String)
          (arguments : List (functionArg))
          (outputType : typeExpr)
          (expressions : List (expr))
  deriving Repr, BEq, Inhabited

  /--
  This syntax represents an Alloy function declaration
  -/
  declare_syntax_cat functionDecl
  syntax "fun" extendedIdent ("["functionArg,*"]")? ":" typeExpr "{"
    expr*
  "}": functionDecl
  syntax "fun" extendedIdent ("("functionArg,*")")? ":" typeExpr "{"
    expr*
  "}": functionDecl

  abbrev FunctionDecl := TSyntax `functionDecl

  namespace functionDecl

    instance : ToString functionDecl where
    toString (fd : functionDecl) : String :=
      s!"functionDecl : \{
            name := {fd.name},
            arguments := {fd.arguments},
            outputType := {fd.outputType},
            expressions := {fd.expressions}
          }"

    /--
    Generates a string representation of the structure
    -/
    def toString (fd : functionDecl) := ToString.toString fd

  end functionDecl

end Alloy
