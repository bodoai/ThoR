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
    Insert the module variables. Thus replacing them with a call to their value.
    -/
    partial def formula.insertModuleVariables
    (f : formula)
    (moduleVariables openVariables : List (String))
    : formula :=
    match f with
      | formula.bracket f =>
        formula.bracket (f.insertModuleVariables moduleVariables openVariables)

      | formula.pred_with_args p args =>
        formula.pred_with_args
          p
          (args.map fun arg =>
            arg.insertModuleVariables moduleVariables openVariables)
      | formula.unaryRelBoolOperation op e =>
        formula.unaryRelBoolOperation
          op
          (e.insertModuleVariables moduleVariables openVariables)
      | formula.unaryLogicOperation op f =>
        formula.unaryLogicOperation
          op
          (f.insertModuleVariables moduleVariables openVariables)
      | formula.binaryLogicOperation op f1 f2 =>
        formula.binaryLogicOperation
          op
          (f1.insertModuleVariables moduleVariables openVariables)
          (f2.insertModuleVariables moduleVariables openVariables)
      | formula.tertiaryLogicOperation op f1 f2 f3 =>
        formula.tertiaryLogicOperation
        op
        (f1.insertModuleVariables moduleVariables openVariables)
        (f2.insertModuleVariables moduleVariables openVariables)
        (f3.insertModuleVariables moduleVariables openVariables)
      | formula.quantification q d n t f =>
        formula.quantification
        q
        d
        n
        (t.insertModuleVariables moduleVariables openVariables)
        (f.map fun f =>
          f.insertModuleVariables moduleVariables openVariables)

      | formula.letDeclaration name value body =>
        formula.letDeclaration
          (name)
          (value.insertModuleVariables moduleVariables openVariables)
          (body.map fun f => f.insertModuleVariables moduleVariables openVariables)

      | formula.relationComarisonOperation op expr1 expr2 =>
        formula.relationComarisonOperation
          op
          (expr1.insertModuleVariables moduleVariables openVariables)
          (expr2.insertModuleVariables moduleVariables openVariables)

      | formula.algebraicComparisonOperation op algExpr1 algExpr2 =>
        formula.algebraicComparisonOperation
          op
          (algExpr1.insertModuleVariables moduleVariables openVariables)
          (algExpr2.insertModuleVariables moduleVariables openVariables)

      | formula.string _ => f

    /--
    Insert the module variables. Thus replacing them with a call to their value.
    -/
    partial def expr.insertModuleVariables
    (e : expr)
    (moduleVariables openVariables : List (String))
    : expr := Id.run do
      match e with
        | expr.bracket e =>
          expr.bracket (e.insertModuleVariables moduleVariables openVariables)

        | expr.string s =>
          if !moduleVariables.contains s then return e

          let index := moduleVariables.idxOf s
          let replacer := openVariables[index]!
          return expr.string replacer

        | expr.unaryRelOperation op e =>
          expr.unaryRelOperation
            op
            (e.insertModuleVariables moduleVariables openVariables)
        | expr.binaryRelOperation op e1 e2 =>
          expr.binaryRelOperation
            op
            (e1.insertModuleVariables moduleVariables openVariables)
            (e2.insertModuleVariables moduleVariables openVariables)
        | expr.dotjoin dj e1 e2 =>
          expr.dotjoin
            dj
            (e1.insertModuleVariables moduleVariables openVariables)
            (e2.insertModuleVariables moduleVariables openVariables)

        | expr.ifElse condition thenBody elseBody =>
          expr.ifElse
            (condition.insertModuleVariables moduleVariables openVariables)
            (thenBody.insertModuleVariables moduleVariables openVariables)
            (elseBody.insertModuleVariables moduleVariables openVariables)

        | expr.function_call_with_args functionName arguments =>
          expr.function_call_with_args
            functionName
            (arguments.map fun a =>
              a.insertModuleVariables moduleVariables openVariables)

        | expr.const _ => e
        | expr.string_rb _ => e
        | expr.callFromOpen _ => e


    /--
    Insert the module variables. Thus replacing them with a call to their value.
    -/
    partial def typeExpr.insertModuleVariables
    (te : typeExpr)
    (moduleVariables openVariables : List (String))
    : typeExpr :=
      match te with
        | typeExpr.arrowExpr ae =>
          typeExpr.arrowExpr (ae.insertModuleVariables moduleVariables openVariables)
        | typeExpr.multExpr m e =>
          typeExpr.multExpr m (e.insertModuleVariables moduleVariables openVariables)
        | typeExpr.relExpr e =>
          typeExpr.relExpr (e.insertModuleVariables moduleVariables openVariables)

    /--
    Insert the module variables. Thus replacing them with a call to their value.
    -/
    partial def arrowOp.insertModuleVariables
    (ao : arrowOp)
    (moduleVariables openVariables : List (String))
    : arrowOp :=
    match ao with
      | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
        arrowOp.multArrowOpExpr
          (e1.insertModuleVariables moduleVariables openVariables)
          m1 m2
          (e2.insertModuleVariables moduleVariables openVariables)

      | arrowOp.multArrowOpExprLeft e1 m1 m2 ae2 =>
        arrowOp.multArrowOpExprLeft
          (e1.insertModuleVariables moduleVariables openVariables)
          m1 m2
          (ae2.insertModuleVariables moduleVariables openVariables)

      | arrowOp.multArrowOpExprRight ae1 m1 m2 e2 =>
        arrowOp.multArrowOpExprRight
          (ae1.insertModuleVariables moduleVariables openVariables)
          m1 m2
          (e2.insertModuleVariables moduleVariables openVariables)

      | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
        arrowOp.multArrowOp
          (ae1.insertModuleVariables moduleVariables openVariables)
          m1 m2
          (ae2.insertModuleVariables moduleVariables openVariables)

    /--
    Insert the module variables. Thus replacing them with a call to their value.
    -/
    partial def algExpr.insertModuleVariables
      (ae : algExpr)
      (moduleVariables openVariables : List (String))
      : algExpr :=
        match ae with
          | algExpr.number _ => ae
          | algExpr.cardExpression e =>
            algExpr.cardExpression
              (e.insertModuleVariables moduleVariables openVariables)
          | algExpr.unaryAlgebraOperation op ae =>
            algExpr.unaryAlgebraOperation
              op
              (ae.insertModuleVariables moduleVariables openVariables)
          | algExpr.binaryAlgebraOperation op ae1 ae2 =>
            algExpr.binaryAlgebraOperation
              op
              (ae1.insertModuleVariables moduleVariables openVariables)
              (ae2.insertModuleVariables moduleVariables openVariables)

  end
end Shared
