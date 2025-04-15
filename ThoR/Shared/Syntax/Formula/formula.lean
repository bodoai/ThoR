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

  syntax ident : formula

  syntax ident ( "[" expr,+ "]") : formula  -- predcall

  syntax:50 "("formula")" : formula

  syntax unRelBoolOp expr : formula

  syntax unLogOp formula: formula

  syntax:60 formula binLogOp formula : formula

  declare_syntax_cat relComparison
  syntax expr relCompareOp expr : relComparison
  --syntax relComparison : formula -- enabeling this causes stack overflow ?

  syntax algExpr algCompareOp algExpr : formula
  syntax quant ("disj")? ident,+ ":" typeExpr "|" "{" (formula)+ "}" : formula
  syntax quant ("disj")? ident,+ ":" typeExpr "|" formula : formula

  /-- alloy let Syntax -/
  declare_syntax_cat alloyLetDecl
  abbrev AlloyLetDecl := TSyntax `alloyLetDecl
  syntax "let" ident "=" formula "|" formula : alloyLetDecl
  syntax "let" ident "=" formula "|" "{" formula* "}" : alloyLetDecl
  syntax alloyLetDecl : formula

  --Special tertiariy Syntax (if else)
  declare_syntax_cat formula_if_connector
  syntax "=>" : formula_if_connector
  syntax formula formula_if_connector formula " else " formula : formula

end Shared
