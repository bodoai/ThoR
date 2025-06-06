/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the mutual data structures-/
import ThoR.Shared.Syntax.Mutuals.mutuals

namespace Shared
  mutual
    /--
    Returns the required definitions for the formula to work in Lean
    -/
    partial def formula.getReqDefinitions
      (f : formula)
      : List (String) := Id.run do
        match f with
          | formula.bracket f => f.getReqDefinitions
          | formula.string s => [s]
          | formula.pred_with_args p _ => [p]
          | formula.unaryRelBoolOperation _ expression =>
            expression.getReqDefinitions
          | formula.unaryLogicOperation _ f => f.getReqDefinitions
          | formula.binaryLogicOperation _ f1 f2 =>
            f1.getReqDefinitions.append f2.getReqDefinitions
          | formula.tertiaryLogicOperation _ f1 f2 f3 =>
            let f1_rd := f1.getReqDefinitions
            let f2_rd := f2.getReqDefinitions
            let f3_rd := f3.getReqDefinitions
            f1_rd ++ f2_rd ++ f3_rd
          | formula.algebraicComparisonOperation _ ae1 ae2 =>
            let ae1_rd := ae1.getReqDefinitions
            let ae2_rd := ae2.getReqDefinitions
            ae1_rd ++ ae2_rd
          | formula.relationComarisonOperation _ expr1 expr2 =>
            let expr1_rd := expr1.getReqDefinitions
            let expr2_rd := expr2.getReqDefinitions
            expr1_rd ++ expr2_rd
          | formula.quantification _ _ n te f =>
            let f_rd := ((f.map fun form =>
              form.getReqDefinitions).join
                ).filter fun (elem) => !(n.contains elem)
            let te_rd := te.getReqDefinitions
            f_rd ++ te_rd
          | formula.letDeclaration _ value body =>
            let value_rd := value.getReqDefinitions
            let body_rds := (body.map fun e => e.getReqDefinitions).join
            body_rds ++ value_rd

    /--
    Returns the required definitions for the expr to work in Lean
    -/
    partial def expr.getReqDefinitions
      (e : expr)
      : List (String) :=
        match e with
          | expr.bracket e => e.getReqDefinitions
          | expr.ifElse condition thenBody elseBody =>
            let condition_rd := condition.getReqDefinitions
            let thenBody_rd := thenBody.getReqDefinitions
            let elseBody_rd := elseBody.getReqDefinitions
            condition_rd ++ thenBody_rd ++ elseBody_rd
          | expr.dotjoin _ expr1 expr2 =>
            let expr1_rd := expr1.getReqDefinitions
            let expr2_rd := expr2.getReqDefinitions
            expr1_rd ++ expr2_rd
          | expr.binaryRelOperation _ expr1 expr2 =>
            let expr1_rd := expr1.getReqDefinitions
            let expr2_rd := expr2.getReqDefinitions
            expr1_rd ++ expr2_rd
          | expr.unaryRelOperation _ expression =>
            expression.getReqDefinitions
          | expr.function_call_with_args _ arguments =>
            (arguments.map fun a => a.getReqDefinitions).join
          | expr.string _ => []
          | expr.string_rb _ => []
          | expr.const _ => []
          | expr.callFromOpen _ => []

    /--
    Returns the required definitions for the typeExpr to work in Lean
    -/
    partial def typeExpr.getReqDefinitions (te : typeExpr) : List (String) :=
      match te with
        | typeExpr.arrowExpr ae => ae.getReqDefinitions
        | typeExpr.multExpr _ e => e.getReqDefinitions
        | typeExpr.relExpr e => e.getReqDefinitions

    /--
    Returns the required definitions for the arrowOp to work in Lean
    -/
    partial def arrowOp.getReqDefinitions (ae : arrowOp) : List (String) :=
      match ae with
        | arrowOp.multArrowOpExpr e1 _ _ e2 =>
          e1.getReqDefinitions ++ e2.getReqDefinitions

        | arrowOp.multArrowOpExprLeft e1 _ _ ae2 =>
          e1.getReqDefinitions ++ ae2.getReqDefinitions

        | arrowOp.multArrowOpExprRight ae1 _ _ e2 =>
          ae1.getReqDefinitions ++ e2.getReqDefinitions

        | arrowOp.multArrowOp ae1 _ _ ae2 =>
          ae1.getReqDefinitions ++ ae2.getReqDefinitions

    /--
    Returns the required definitions for the algExpr to work in Lean
    -/
    partial def algExpr.getReqDefinitions
      (ae : algExpr)
      : List (String) := Id.run do
        match ae with
          | algExpr.number _ => []
          | algExpr.cardExpression e => e.getReqDefinitions
          | algExpr.unaryAlgebraOperation _ ae => ae.getReqDefinitions
          | algExpr.binaryAlgebraOperation _ ae1 ae2 =>
            ae1.getReqDefinitions ++ ae2.getReqDefinitions

  end
end Shared
