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
    Generates a syntax representation of the type expr (unrelated to a block)
    -/
    partial def expr.toSyntaxOutsideBlock
      (e : expr)
      : Expression := Unhygienic.run do
        match e with
          | expr.const c => `(expr | $(c.toSyntax):constant)

          | expr.string s => `(expr | $(mkIdent s.toName):ident)

          | expr.function_call_with_args functionName arguments =>
            let arguments :=
              (arguments.map fun arg => arg.toSyntaxOutsideBlock)
            let mut argument_array := #[]
            for a in arguments do
              argument_array :=
                argument_array.push
                  (← `(expr_without_if | ($a:expr)))
            `(expr | $(mkIdent functionName.toName):ident [$argument_array,*])

          | expr.callFromOpen sn => `(expr| $(sn.toSyntax):separatedNamespace)

          | expr.unaryRelOperation op e =>
            `(expr | $(op.toSyntax):unRelOp ($(e.toSyntaxOutsideBlock):expr))

          | expr.binaryRelOperation op e1 e2 =>
            `(expr |
              ($(e1.toSyntaxOutsideBlock):expr)
              $(op.toSyntax):binRelOp
              ($(e2.toSyntaxOutsideBlock):expr)
            )

          | expr.dotjoin dj e1 e2 =>
            `(expr |
              ($(e1.toSyntaxOutsideBlock):expr)
              $(dj.toSyntax):dotjoin
              ($(e2.toSyntaxOutsideBlock):expr)
            )

          | expr.ifElse condition thenBody elseBody =>
            let connector ← `(expr_if_connector | =>)

            `(expr |
              if
              ($(condition.toSyntaxOutsideBlock):formula)
              $connector:expr_if_connector
              $(thenBody.toSyntaxOutsideBlock):expr
              else
              $(elseBody.toSyntaxOutsideBlock):expr
            )

          -- FIXME In der folgenden Zeile fehlt noch das $rb -> Macht das Probleme?
          | expr.string_rb s =>
            let components :=
              (s.splitOn ".").map fun n => n.toName

            let name := Name.fromComponents components
            let identifier := mkIdent name
            `(expr| @$(identifier):ident)

    /--
    Generates a syntax representation of the type formula (unrelated to a block)
    -/
    partial def formula.toSyntaxOutsideBlock
      (f : formula)
      : Formula := Unhygienic.run do
        match f with
          | formula.string s =>
            `(formula | $(mkIdent s.toName):ident)

          | formula.pred_with_args pred_name arguments =>
            let arguments :=
              (arguments.map fun a => a.toSyntaxOutsideBlock).toArray
            `(formula |
              $(mkIdent pred_name.toName):ident [ $[$arguments:expr],* ])

          | formula.unaryRelBoolOperation op expression =>
            `(formula |
              $(op.toSyntax):unRelBoolOp $(expression.toSyntaxOutsideBlock):expr)

          | formula.unaryLogicOperation op formula' =>
            `(formula |
              $(op.toSyntax):unLogOp
              ($(formula'.toSyntaxOutsideBlock):formula))

          | formula.binaryLogicOperation op formula1 formula2 =>
            `(formula |
              ($(formula1.toSyntaxOutsideBlock):formula)
              $(op.toSyntax):binLogOp
              ($(formula2.toSyntaxOutsideBlock):formula)
            )

          -- currently only ifElse
          | formula.tertiaryLogicOperation _ formula1 formula2 formula3 =>
            let c ← `(formula_if_connector | =>)
            `(formula |
              if
              $(formula1.toSyntaxOutsideBlock):formula
              $c:formula_if_connector
              $(formula2.toSyntaxOutsideBlock):formula
              else
              $(formula3.toSyntaxOutsideBlock):formula
            )

          | formula.algebraicComparisonOperation op algExpr1 algExpr2 =>
            `(formula |
              $(algExpr1.toSyntaxOutsideBlock):algExpr
              $(op.toSyntax):algCompareOp
              $(algExpr2.toSyntaxOutsideBlock):algExpr
            )

          | formula.quantification
            quantifier
            disjunction
            names
            typeExpression
            formulas =>
            let names := (names.map fun n => mkIdent n.toName).toArray
            let formulas :=
              (formulas.map fun f => f.toSyntaxOutsideBlock).toArray

            if disjunction then
              `(formula |
                $(quantifier.toSyntax):quant
                disj
                $[$names:ident],* :
                $(typeExpression.toSyntaxOutsideBlock):typeExpr |
                { $[$formulas:formula]* }
              )
            else
              `(formula |
                $(quantifier.toSyntax):quant
                $[$names:ident],* :
                $(typeExpression.toSyntaxOutsideBlock):typeExpr |
                { $[$formulas:formula]* }
              )

          | formula.letDeclaration name value body =>
            let body := (body.map fun f => f.toSyntaxOutsideBlock).toArray

            let letSyntax ← `(alloyLetDecl |
              let $(mkIdent name) = ($(value.toSyntaxOutsideBlock):formula) |
              { $[$body:formula]* }
            )
            `(formula | $letSyntax:alloyLetDecl)

          | formula.relationComarisonOperation op expr1 expr2 =>
            `(formula |
              ($(expr1.toSyntaxOutsideBlock):expr)
              $(op.toSyntax):relCompareOp
              ($(expr2.toSyntaxOutsideBlock):expr)
            )

    /--
    Generates a syntax representation of the type algExpr (unrelated to a block)
    -/
    partial def algExpr.toSyntaxOutsideBlock
      (ae : algExpr)
      : AlgExpr := Unhygienic.run do
        match ae with
          | algExpr.number n => `(algExpr | $(Syntax.mkNumLit s!"{n}"):num)
          | algExpr.cardExpression e => `(algExpr | # $(e.toSyntaxOutsideBlock):expr)

          | algExpr.unaryAlgebraOperation op ae =>
            `(algExpr | $(op.toSyntax):unAlgOp $(ae.toSyntaxOutsideBlock):algExpr)

          | algExpr.binaryAlgebraOperation op ae1 ae2 =>
            `(algExpr |
              $(op.toSyntax):binAlgOp [
              $(ae1.toSyntaxOutsideBlock):algExpr,
              $(ae2.toSyntaxOutsideBlock):algExpr] )

    /--
    Generates a syntax representation of the type typeExpr (unrelated to a block)
    -/
    partial def typeExpr.toSyntaxOutsideBlock
    (te: typeExpr)
    : TypeExpr := Unhygienic.run do
      match te with
        | typeExpr.arrowExpr ae => `(typeExpr| $(ae.toSyntaxOutsideBlock):arrowOp)
        | typeExpr.multExpr m e => `(typeExpr| $(m.toSyntax):mult $(e.toSyntaxOutsideBlock):expr)
        | typeExpr.relExpr e => `(typeExpr| $(e.toSyntaxOutsideBlock):expr)

    /--
    Generates a syntax representation of the type arrowOp (unrelated to a block)
    -/
    partial def arrowOp.toSyntaxOutsideBlock
      (ao : arrowOp)
      : ArrowOp := Unhygienic.run do
        match ao with
          | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
            `(arrowOp|
              $(e1.toSyntaxOutsideBlock):expr
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(e2.toSyntaxOutsideBlock):expr)

          | arrowOp.multArrowOpExprLeft e1 m1 m2 ae2 =>
            `(arrowOp|
              $(e1.toSyntaxOutsideBlock):expr
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(ae2.toSyntaxOutsideBlock):arrowOp)

          | arrowOp.multArrowOpExprRight ae1 m1 m2 e2 =>
            `(arrowOp|
              $(ae1.toSyntaxOutsideBlock):arrowOp
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(e2.toSyntaxOutsideBlock):expr)

          | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
            `(arrowOp|
              $(ae1.toSyntaxOutsideBlock):arrowOp
              $(m1.toSyntax):mult → $(m2.toSyntax):mult
              $(ae2.toSyntaxOutsideBlock):arrowOp)

  end

end Shared
