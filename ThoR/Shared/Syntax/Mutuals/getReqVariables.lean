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
    Gets the required variables for the type expr
    -/
    partial def expr.getReqVariables
      (e : expr)
      : List (String) :=
        match e with
          | expr.bracket e => e.getReqVariables

          | expr.string s => [s]

          | expr.callFromOpen sn => Id.run do
            -- this String can be something like m1.A
            let sns := sn.representedNamespace.getId.toString
            let snsSplit := sns.splitOn "."
            if snsSplit.isEmpty then
              return [sns]
            else
              [snsSplit.getLast!]

          | expr.unaryRelOperation _ e => e.getReqVariables

          | expr.binaryRelOperation _ e1 e2 =>
            (e1.getReqVariables) ++ (e2.getReqVariables)

          | expr.dotjoin _ e1 e2 =>
            (e1.getReqVariables) ++ (e2.getReqVariables)

          | expr.ifElse condition thenBody elseBody =>
            (condition.getReqVariables) ++
            (thenBody.getReqVariables) ++
            (elseBody.getReqVariables)

          | expr.function_call_with_args _ arguments =>
            (arguments.map fun a => a.getReqVariables).join

          | expr.string_rb _ => []
          | expr.const _ => []

    /--
    Gets the required variables for the type expr formula
    -/
    partial def formula.getReqVariables
      (f : formula)
      : List (String) :=
        match f with
          | formula.bracket f => f.getReqVariables

          | formula.pred_with_args _ pa =>
            (pa.map fun (e) => e.getReqVariables).join

          | formula.unaryRelBoolOperation _ e => e.getReqVariables

          | formula.unaryLogicOperation _ f => f.getReqVariables

          | formula.binaryLogicOperation _ f1 f2 =>
            f1.getReqVariables ++ f2.getReqVariables

          | formula.tertiaryLogicOperation _ f1 f2 f3 =>
            f1.getReqVariables ++ f2.getReqVariables ++ f3.getReqVariables

          | formula.algebraicComparisonOperation _ ae1 ae2 =>
            ae1.getReqVariables ++ ae2.getReqVariables

          | formula.relationComarisonOperation _ e1 e2 =>
            e1.getReqVariables ++ e2.getReqVariables

          | formula.quantification _ _ n e f =>
            (((f.map fun form =>
              form.getReqVariables).join)
              ++ e.getReqVariables).filter
              fun (elem) => !(n.contains elem) -- quantor vars are not required

          | formula.letDeclaration name value body =>
            let value_rv := value.getReqVariables
            let body_rvs :=
              (body.map fun e => e.getReqVariables).join.filter
                -- the name is not required in the body
                fun elem => !(name.toString == elem)
            body_rvs ++ value_rv

          | formula.string _ => []
    /--
    Gets the required variables for the type arrowOp
    -/
    partial def arrowOp.getReqVariables (ae : arrowOp) : List (String) :=
      match ae with
        | arrowOp.multArrowOpExpr e1 _ _ e2 =>
          e1.getReqVariables ++ e2.getReqVariables

        | arrowOp.multArrowOpExprLeft e1 _ _ ae2 =>
          e1.getReqVariables ++ ae2.getReqVariables

        | arrowOp.multArrowOpExprRight ae1 _ _ e2 =>
          ae1.getReqVariables ++ e2.getReqVariables

        | arrowOp.multArrowOp ae1 _ _ ae2 =>
          ae1.getReqVariables ++ ae2.getReqVariables

    /--
    Gets the required variables for the type typeExpr
    -/
    partial def typeExpr.getReqVariables (te : typeExpr) : List (String) :=
      match te with
        | typeExpr.arrowExpr ae => ae.getReqVariables
        | typeExpr.multExpr _ e => e.getReqVariables
        | typeExpr.relExpr e => e.getReqVariables

    /--
    Gets the required variables for the type algExpr
    -/
    partial def algExpr.getReqVariables
      (ae : algExpr)
      : List (String) := Id.run do
        match ae with
          | algExpr.number _ => []
          | algExpr.cardExpression e => e.getReqVariables
          | algExpr.unaryAlgebraOperation _ ae => ae.getReqVariables
          | algExpr.binaryAlgebraOperation _ ae1 ae2 =>
            ae1.getReqVariables ++ ae2.getReqVariables
  end
end Shared
