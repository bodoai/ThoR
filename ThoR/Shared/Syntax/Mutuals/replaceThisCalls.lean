/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the mutual data structures -/
import ThoR.Shared.Syntax.Mutuals.mutuals

import ThoR.Alloy.Syntax.SeparatedNamespace.separatedNamespace

open Lean
open Alloy

namespace Shared
  mutual
    /--
    replaces calls to "this" (current module), with a call to the given module
    name.
    -/
    partial def expr.replaceThisCalls
      (e : expr)
      (moduleName : String)
      : expr := Id.run do
        match e with
          | expr.bracket e =>
            expr.bracket (e.replaceThisCalls moduleName)

          | expr.callFromOpen sn =>
            let components := sn.representedNamespace.getId.components
            if !components[0]! == `this then return e
            let moduleName := (moduleName.splitOn "_").getLast!
            let new_components := [moduleName.toName] ++ (components.drop 1)
            let new_ident := mkIdent (Name.fromComponents new_components)

            expr.callFromOpen
              (separatedNamespace.mk new_ident)

          | expr.unaryRelOperation op e =>
            expr.unaryRelOperation
              op
              (e.replaceThisCalls moduleName)

          | expr.binaryRelOperation op e1 e2 =>
            expr.binaryRelOperation
              op
              (e1.replaceThisCalls moduleName)
              (e2.replaceThisCalls moduleName)

          | expr.dotjoin dj e1 e2 =>
            expr.dotjoin
              dj
              (e1.replaceThisCalls moduleName)
              (e2.replaceThisCalls moduleName)

          | expr.function_call_with_args functionName arguments =>
            expr.function_call_with_args
              functionName
              (arguments.map fun a => a.replaceThisCalls moduleName)

          | expr.ifElse condition thenBody elseBody =>
            expr.ifElse
              (condition.replaceThisCalls moduleName)
              (thenBody.replaceThisCalls moduleName)
              (elseBody.replaceThisCalls moduleName)

          | expr.string _ => e
          | expr.string_rb _ => e
          | expr.const _ => e

    /--
    replaces calls to "this" (current module), with a call to the given module
    name.
    -/
    partial def formula.replaceThisCalls
      (f : formula)
      (moduleName : String)
      : formula :=
      match f with
        | formula.bracket f =>
          formula.bracket (f.replaceThisCalls moduleName)

        | formula.pred_with_args p args =>
          formula.pred_with_args
            p
            (args.map fun arg =>
              arg.replaceThisCalls moduleName)
        | formula.unaryRelBoolOperation op e =>
          formula.unaryRelBoolOperation
            op
            (e.replaceThisCalls moduleName)
        | formula.unaryLogicOperation op f =>
          formula.unaryLogicOperation
            op
            (f.replaceThisCalls moduleName)
        | formula.binaryLogicOperation op f1 f2 =>
          formula.binaryLogicOperation
            op
            (f1.replaceThisCalls moduleName)
            (f2.replaceThisCalls moduleName)
        | formula.tertiaryLogicOperation op f1 f2 f3 =>
          formula.tertiaryLogicOperation
            op
            (f1.replaceThisCalls moduleName)
            (f2.replaceThisCalls moduleName)
            (f3.replaceThisCalls moduleName)
        | formula.quantification q d n t f =>
          formula.quantification
            q
            d
            n
            (t.replaceThisCalls moduleName)
            (f.map fun f =>
              f.replaceThisCalls moduleName)

        | formula.letDeclaration name value body =>
          formula.letDeclaration
            (name)
            (value.replaceThisCalls moduleName)
            (body.map fun f => f.replaceThisCalls moduleName)

        | formula.relationComarisonOperation op expression1 expression2 =>
          formula.relationComarisonOperation
            op
            (expression1.replaceThisCalls moduleName)
            (expression2.replaceThisCalls moduleName)

        | formula.algebraicComparisonOperation op algExpression1 algExpression2 =>
          formula.algebraicComparisonOperation
            op
            (algExpression1.replaceThisCalls moduleName)
            (algExpression2.replaceThisCalls moduleName)

        | formula.string _ => f

    /--
    replaces calls to "this" (current module), with a call to the given module
    name.
    -/
    partial def algExpr.replaceThisCalls
      (ae : algExpr)
      (moduleName : String)
      : algExpr :=
      match ae with
        | algExpr.number _ => ae

        | algExpr.cardExpression e =>
          algExpr.cardExpression (e.replaceThisCalls moduleName)

        | algExpr.unaryAlgebraOperation op ae =>
          algExpr.unaryAlgebraOperation op (ae.replaceThisCalls moduleName)

        | algExpr.binaryAlgebraOperation op ae1 ae2 =>
          algExpr.binaryAlgebraOperation
            op
            (ae1.replaceThisCalls moduleName)
            (ae2.replaceThisCalls moduleName)

    /--
    replaces calls to "this" (current module), with a call to the given module
    name.
    -/
    partial def typeExpr.replaceThisCalls
      (te : typeExpr)
      (moduleName : String)
      : typeExpr :=
      match te with
        | typeExpr.arrowExpr ae =>
          typeExpr.arrowExpr (ae.replaceThisCalls moduleName)
        | typeExpr.multExpr m e =>
          typeExpr.multExpr m (e.replaceThisCalls moduleName)
        | typeExpr.relExpr e =>
          typeExpr.relExpr (e.replaceThisCalls moduleName)

    /--
    replaces calls to "this" (current module), with a call to the given module
    name.
    -/
    partial def arrowOp.replaceThisCalls
      (ao : arrowOp)
      (moduleName : String)
      : arrowOp :=
      match ao with
        | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
          arrowOp.multArrowOpExpr
            (e1.replaceThisCalls moduleName)
            m1 m2
            (e2.replaceThisCalls moduleName)

        | arrowOp.multArrowOpExprLeft e1 m1 m2 ae2 =>
          arrowOp.multArrowOpExprLeft
            (e1.replaceThisCalls moduleName)
            m1 m2
            (ae2.replaceThisCalls moduleName)

        | arrowOp.multArrowOpExprRight ae1 m1 m2 e2 =>
          arrowOp.multArrowOpExprRight
            (ae1.replaceThisCalls moduleName)
            m1 m2
            (e2.replaceThisCalls moduleName)

        | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
          arrowOp.multArrowOp
            (ae1.replaceThisCalls moduleName)
            m1 m2
            (ae2.replaceThisCalls moduleName)

  end
end Shared
