/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the data structures-/
import ThoR.Shared.Syntax.Mutuals.mutuals

namespace Shared

  mutual
    /--
    changes an expr (and all of its subexprs)
    to a string rb expression (if they are string)
    -/
    partial def expr.toStringRb (e : expr) : expr :=
      match e with
        | expr.bracket e => expr.bracket (e.toStringRb)
        | expr.string s => expr.string_rb s
        | expr.binaryRelOperation op e1 e2 =>
          expr.binaryRelOperation op (e1.toStringRb) (e2.toStringRb)
        | expr.unaryRelOperation op e =>
          expr.unaryRelOperation op (e.toStringRb)
        | expr.dotjoin dj e1 e2 =>
          expr.dotjoin dj (e1.toStringRb) (e2.toStringRb)
        | expr.ifElse condition thenBody elseBody =>
          expr.ifElse (condition.toStringRb) (thenBody.toStringRb) (elseBody.toStringRb)
        | expr.function_call_with_args functionName arguments =>
          expr.function_call_with_args functionName (arguments.map fun a => a.toStringRb)
        | expr.string_rb _ => e
        | expr.callFromOpen _ => e
        | expr.const _ => e

    /--
    changes all contained expr
    to a string rb expression (if they are string)
    -/
    partial def formula.toStringRb
      (f: formula)
      : formula :=
        match f with
          | formula.bracket f =>
            formula.bracket (f.toStringRb)

          | formula.string _ => f

          | formula.pred_with_args n pas =>
            formula.pred_with_args
              n
              (pas.map fun pa =>
                pa.toStringRb)

          | formula.unaryRelBoolOperation op e =>
            formula.unaryRelBoolOperation
              op
              (e.toStringRb)

          | formula.unaryLogicOperation op f =>
            formula.unaryLogicOperation
              op
              (f.toStringRb)

          | formula.binaryLogicOperation op f1 f2 =>
            formula.binaryLogicOperation
              op
              (f1.toStringRb)
              (f2.toStringRb)

          | formula.tertiaryLogicOperation op f1 f2 f3 =>
            formula.tertiaryLogicOperation
              op
              (f1.toStringRb)
              (f2.toStringRb)
              (f3.toStringRb)

          | formula.algebraicComparisonOperation op ae1 ae2 =>
            formula.algebraicComparisonOperation
              op
              (ae1.toStringRb)
              (ae2.toStringRb)

          | formula.relationComarisonOperation op e1 e2 =>
            formula.relationComarisonOperation
              op
              (e1.toStringRb)
              (e2.toStringRb)

          | formula.quantification q d n te forms =>
            formula.quantification
              q
              d
              n
              (te.toStringRb)
              (forms.map fun f => f.toStringRb)

          | formula.letDeclaration name value body =>
            formula.letDeclaration
              name
              (value.toStringRb)
              (body.map fun f => f.toStringRb)

    /--
    changes all contained expr
    to a string rb expression (if they are string)
    -/
    partial def typeExpr.toStringRb
      (te: typeExpr)
      : typeExpr := Id.run do
        match te with
          | typeExpr.arrowExpr ae =>
            typeExpr.arrowExpr
              (ae.toStringRb)
          | typeExpr.multExpr m e =>
            typeExpr.multExpr
              m
              (e.toStringRb)
          | typeExpr.relExpr e =>
            typeExpr.relExpr
              (e.toStringRb)

    /--
    changes all contained expr
    to a string rb expression (if they are string)
    -/
    partial def algExpr.toStringRb
      (ae : algExpr)
      : algExpr :=
        match ae with
          | algExpr.number _ => ae

          | algExpr.cardExpression e =>
            algExpr.cardExpression (e.toStringRb)

          | algExpr.unaryAlgebraOperation op ae =>
            algExpr.unaryAlgebraOperation op (ae.toStringRb)

          | algExpr.binaryAlgebraOperation op ae1 ae2 =>
            algExpr.binaryAlgebraOperation op (ae1.toStringRb) (ae2.toStringRb)

    /--
    changes all contained expr
    to a string rb expression (if they are string)
    -/
    partial def arrowOp.toStringRb
      (ao: arrowOp)
      : arrowOp :=
        match ao with
          | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
            arrowOp.multArrowOpExpr
              (e1.toStringRb)
              m1
              m2
              (e2.toStringRb)

          | arrowOp.multArrowOpExprLeft e m1 m2 ao1 =>
            arrowOp.multArrowOpExprLeft
              (e.toStringRb)
              m1
              m2
              (ao1.toStringRb)

          | arrowOp.multArrowOpExprRight ao1 m1 m2 e =>
            arrowOp.multArrowOpExprRight
              (ao1.toStringRb)
              m1
              m2
              (e.toStringRb)

          | arrowOp.multArrowOp ao1 m1 m2 ao2 =>
            arrowOp.multArrowOp
              (ao1.toStringRb)
              m1
              m2
              (ao2.toStringRb)

  end

end Shared
