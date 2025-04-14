/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
an alloy formula is used as the body of predicates, facts and asserts
-/

import ThoR.Shared.Syntax.Mutuals.mutuals
import ThoR.Shared.Syntax.Relation.Expr.expr
import ThoR.Shared.Syntax.Algebra.AlgExpr.algExpr
import ThoR.Shared.Syntax.TypeExpr.typeExpr

open Lean
namespace Shared

  declare_syntax_cat formula_without_if
  abbrev Formula_without_if := TSyntax `formula_without_if
  syntax ident : formula_without_if

  syntax ident ( "[" expr,+ "]") : formula_without_if  -- predcall

  syntax:50 "("formula_without_if")" : formula_without_if

  syntax unRelBoolOp expr : formula_without_if

  syntax unLogOp formula_without_if: formula_without_if

  syntax:60 formula_without_if binLogOp formula_without_if : formula_without_if
  syntax expr relCompareOp expr : formula_without_if

  syntax algExpr algCompareOp algExpr : formula_without_if
  syntax quant ("disj")? ident,+ ":" typeExpr "|" "{" (formula_without_if)+ "}" : formula_without_if
  syntax quant ("disj")? ident,+ ":" typeExpr "|" formula_without_if : formula_without_if

  /-- alloy let Syntax -/
  declare_syntax_cat alloyLetDecl
  abbrev AlloyLetDecl := TSyntax `alloyLetDecl
  syntax "let" ident "=" formula_without_if "|" formula_without_if : alloyLetDecl
  syntax "let" ident "=" formula_without_if "|" "{" formula_without_if* "}" : alloyLetDecl
  syntax alloyLetDecl : formula_without_if

  syntax formula_without_if : formula

  --Special tertiariy Syntax (if else)
  syntax formula " => " formula " else " formula : formula

end Shared
