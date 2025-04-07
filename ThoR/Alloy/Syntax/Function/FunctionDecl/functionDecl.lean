/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Alloy.Syntax.Function.FunctionArg.functionArg
import ThoR.Alloy.Syntax.SeparatedNamespace.extendedIdent
import ThoR.Shared.Syntax.Formula.formula
import ThoR.Alloy.Syntax.Function.FunctionIfDecl.functionIfDecl

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
          (ifExpressions : List (functionIfDecl))
  deriving Repr, BEq, Inhabited

  /--
  This syntax represents an Alloy function declaration
  -/
  declare_syntax_cat functionDecl
  abbrev FunctionDecl := TSyntax `functionDecl

  declare_syntax_cat exprOfFunIfDecl
  abbrev ExprOfFunIfDecl := TSyntax `exprOfFunIfDecl
  syntax expr : exprOfFunIfDecl
  syntax functionIfDecl : exprOfFunIfDecl


  syntax (name := function_declaration_with_brackets)
    "fun" extendedIdent ("["functionArg,*"]")? ":" typeExpr "{"
      exprOfFunIfDecl*
    "}": functionDecl

  syntax (name := function_declaration_with_parenthesis)
    "fun" extendedIdent ("("functionArg,*")")? ":" typeExpr "{"
      exprOfFunIfDecl*
    "}": functionDecl

  namespace functionDecl

    instance : ToString functionDecl where
    toString (fd : functionDecl) : String :=
      s!"functionDecl : \{
            name := {fd.name},
            arguments := {fd.arguments},
            outputType := {fd.outputType},
            {
            if !fd.expressions.isEmpty then
              s!"expressions := {fd.expressions},"
            else ""
            }
            {
            if !fd.ifExpressions.isEmpty then
              s!"ifExpressions := {fd.ifExpressions}"
            else ""
            }
          }"

    /--
    Generates a string representation of the structure
    -/
    def toString (fd : functionDecl) := ToString.toString fd

  end functionDecl

end Alloy
