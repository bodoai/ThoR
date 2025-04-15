/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the data structures-/
import ThoR.Shared.Syntax.Mutuals.mutuals

/- import of the syntax for expr -/
import ThoR.Shared.Syntax.Relation.Expr.expr

/- import of the syntax for algExpr -/
import ThoR.Shared.Syntax.Algebra.AlgExpr.algExpr

/- import of the syntax for typeExpr -/
import ThoR.Shared.Syntax.TypeExpr.typeExpr

/- import of the syntax for formula -/
import ThoR.Shared.Syntax.Formula.formula

import Lean

open Lean

namespace Shared

  mutual

    /--
    Generates a syntax representation of the type expr
    -/
    partial def expr.toSyntax
      (e : expr)
      (blockName : Name)
      : Expression := Unhygienic.run do
        match e with
          | expr.const c => `(expr | $(c.toSyntax):constant)
          | expr.string s => `(expr | $(mkIdent s.toName):ident)
          | expr.callFromOpen sn => `(expr | $(sn.toSyntax):separatedNamespace)

          | expr.function_call_with_args function_name arguments =>
            let argument_array :=
              (arguments.map fun arg => arg.toSyntax blockName).toArray
            `(expr | $(mkIdent function_name.toName):ident [$argument_array,*])

          | expr.unaryRelOperation op e =>
            `(expr | $(op.toSyntax):unRelOp $(e.toSyntax blockName):expr)

          | expr.binaryRelOperation op e1 e2 =>
            `(expr |
              $(e1.toSyntax blockName):expr
              $(op.toSyntax):binRelOp
              $(e2.toSyntax blockName):expr)

          | expr.dotjoin dj e1 e2 =>
            `(expr |
              $(e1.toSyntax blockName):expr
              $(dj.toSyntax):dotjoin
              $(e2.toSyntax blockName):expr)

          | expr.ifElse condition thenBody elseBody =>
            let c ← `(expr_if_connector | =>)
            `(expr |
              $(condition.toSyntax blockName):formula $c:expr_if_connector
              $(thenBody.toSyntax blockName):expr else
              $(elseBody.toSyntax blockName))

          -- FIXME In der folgenden Zeile fehlt noch das $rb -> Macht das Probleme?
          | expr.string_rb s =>
            let components :=
              [blockName, `vars] ++
              (s.splitOn ".").map fun n => n.toName

            let name := Name.fromComponents components
            let identifier := mkIdent name
            `(expr | @$(identifier):ident)

    /--
    Generates a syntax representation of the type formula
    -/
    partial def formula.toSyntax
      (f : formula)
      (blockName : Name)
      : Formula := Unhygienic.run do
        match f with
          | formula.string s => `(formula | $(mkIdent s.toName):ident)

          | formula.pred_with_args pred_name arguments =>
            let arguments :=
              (arguments.map fun a => a.toSyntax blockName).toArray
            `(formula |
              $(mkIdent pred_name.toName):ident [ $[$arguments:expr],* ])

          | formula.unaryRelBoolOperation op expression =>
            `(formula |
              $(op.toSyntax):unRelBoolOp $(expression.toSyntax blockName):expr)

          | formula.unaryLogicOperation op formula' =>
            `(formula |
              $(op.toSyntax):unLogOp $(formula'.toSyntax blockName):formula)

          | formula.binaryLogicOperation op formula1 formula2 =>
            `(formula |
              $(formula1.toSyntax blockName):formula
              $(op.toSyntax):binLogOp
              $(formula2.toSyntax blockName):formula
            )

          -- currently only ifElse
          | formula.tertiaryLogicOperation _ formula1 formula2 formula3 =>
            let c ← `(formula_if_connector | =>)
            `(formula |
              $(formula1.toSyntax blockName):formula
              $c:formula_if_connector
              $(formula2.toSyntax blockName):formula
              else
              $(formula3.toSyntax blockName):formula
            )

          | formula.algebraicComparisonOperation op algExpr1 algExpr2 =>
            `(formula |
              $(algExpr1.toSyntax blockName):algExpr
              $(op.toSyntax):algCompareOp
              $(algExpr2.toSyntax blockName):algExpr
            )

          | formula.quantification
            quantifier
            disjunction
            names
            typeExpression
            formulas =>
            let names := (names.map fun n => mkIdent n.toName).toArray
            let formulas := (formulas.map fun f => f.toSyntax blockName).toArray
            if disjunction then
              `(formula |
                $(quantifier.toSyntax):quant
                disj
                $[$names:ident],* :
                $(typeExpression.toSyntax blockName):typeExpr |
                { $[$formulas:formula]* }
              )
            else
              `(formula |
                $(quantifier.toSyntax):quant
                $[$names:ident],* :
                $(typeExpression.toSyntax blockName):typeExpr |
                { $[$formulas:formula]* }
              )

          | formula.letDeclaration name value body =>
            let body := (body.map fun f => f.toSyntax blockName).toArray
            let letSyntax ← `(alloyLetDecl |
              let $(mkIdent name) = $(value.toSyntax blockName) |
              { $[$body:formula]* }
            )
            `(formula | $letSyntax:alloyLetDecl)

          | formula.relationComarisonOperation op expr1 expr2 =>
            `(formula |
              rc
              $(expr1.toSyntax blockName):expr
              $(op.toSyntax):relCompareOp
              $(expr2.toSyntax blockName):expr
            )

    /--
    Generates syntax corosponding to the type arrowOp
    -/
    partial def arrowOp.toSyntax
      (ao : arrowOp)
      (blockName : Name)
      : ArrowOp := Unhygienic.run do
        match ao with
          | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
            `(arrowOp|
              $(e1.toSyntax blockName):expr
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(e2.toSyntax blockName):expr)

          | arrowOp.multArrowOpExprLeft e1 m1 m2 ae2 =>
            `(arrowOp|
              $(e1.toSyntax blockName):expr
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(ae2.toSyntax blockName):arrowOp)

          | arrowOp.multArrowOpExprRight ae1 m1 m2 e2 =>
            `(arrowOp|
              $(ae1.toSyntax blockName):arrowOp
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(e2.toSyntax blockName):expr)

          | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
            `(arrowOp|
              $(ae1.toSyntax blockName):arrowOp
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(ae2.toSyntax blockName):arrowOp)

    /--
    Generates a syntax representation of the type algExpr
    -/
    partial def algExpr.toSyntax
      (ae : algExpr)
      (blockName : Name)
      : AlgExpr := Unhygienic.run do
        match ae with
          | algExpr.number n => `(algExpr | $(Syntax.mkNumLit s!"{n}"):num)
          | algExpr.cardExpression e => `(algExpr | # $(e.toSyntax blockName):expr)

          | algExpr.unaryAlgebraOperation op ae =>
            `(algExpr | $(op.toSyntax):unAlgOp $(ae.toSyntax blockName):algExpr)

          | algExpr.binaryAlgebraOperation op ae1 ae2 =>
            `(algExpr |
              $(op.toSyntax):binAlgOp [
              $(ae1.toSyntax blockName):algExpr,
              $(ae2.toSyntax blockName):algExpr] )

    /--
    Generates syntax corosponding to the type typeExpr
    -/
    partial def typeExpr.toSyntax
      (te: typeExpr)
      (blockName : Name)
      : TypeExpr := Unhygienic.run do
        match te with
          | typeExpr.arrowExpr ae => `(typeExpr| $(ae.toSyntax blockName):arrowOp)
          | typeExpr.multExpr m e => `(typeExpr| $(m.toSyntax):mult $(e.toSyntax blockName):expr)
          | typeExpr.relExpr e => `(typeExpr| $(e.toSyntax blockName):expr)

  end

end Shared
