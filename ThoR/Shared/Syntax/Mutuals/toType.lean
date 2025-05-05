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

open Lean

namespace Shared
  mutual
  /--
  Transforms an expr_without_if to an expr via the
  shortcut of adding parenthesis
  -/
  private partial def expr_without_if_to_expr
    (e : Expression_without_if)
    : Expression := Unhygienic.run do
      return ← `(expr | ( $e:expr_without_if ))

  /--
  Parses an expr_without_if syntax to an expr data strucutre
  -/
  partial def expr.toType_without_if
    (e : Expression_without_if)
    (signatureRelationNames : List String := [])
    : Except String expr := do
      match e with
        | `(expr_without_if | ( $e:expr_without_if )) =>
          return ← expr.toType_without_if e signatureRelationNames

        | `(expr_without_if | ( $e:expr )) =>
          return ← expr.toType e signatureRelationNames

        | `(expr_without_if | $const:constant) =>
            return expr.const (← constant.toType const)

        | `(expr_without_if | $name:ident) =>
            let parsedName := name.getId

            if parsedName.isAtomic then

              let exprStringName := name.getId.toString

              -- If the string (name) of the expr is a sigField in a sigFact
              if (signatureRelationNames.contains exprStringName) then
                return expr.dotjoin
                  dotjoin.dot_join
                  (expr.string "this")
                  (expr.string exprStringName)

              else
                return expr.string exprStringName

            else -- ident contains . which must be parsed as dotjoin
              let x := (parsedName.splitAt (parsedName.components.length - 1))
              let subExpr1 := x.1
              let subExpr2 := x.2

              let subE1 : Expression := Unhygienic.run
                `(expr| $(mkIdent subExpr1): ident)

              let subE2 : Expression := Unhygienic.run
                `(expr| $(mkIdent subExpr2): ident)

              return expr.dotjoin
                dotjoin.dot_join
                (← expr.toType subE1 signatureRelationNames)
                (← expr.toType subE2 signatureRelationNames)

        | `(expr_without_if | $sn:separatedNamespace) =>
            let sn ← Alloy.separatedNamespace.toType sn
            let components := sn.representedNamespace.getId.components
            let lastComponent := components.getLast!
            let lastComponentString := lastComponent.toString

            let split := lastComponentString.splitOn "<:"
            let splitNames := split.map fun c => c.toName
            let newComponents := (components.take (components.length - 1)) ++ splitNames
            let newName := Name.fromComponents newComponents
            let newIdent := mkIdent newName
            return expr.callFromOpen (Alloy.separatedNamespace.mk newIdent)

        | `(expr_without_if |
            $called_function:ident
            [ $arguments:expr_without_if,* ]
          ) =>
          let mut arguments_typed := []
          for argument in arguments.getElems do
            arguments_typed :=
              arguments_typed.concat (← expr.toType_without_if argument signatureRelationNames)

          return expr.function_call_with_args
            called_function.getId.toString
            arguments_typed

        | `(expr_without_if |
            $subExpr1:expr_without_if
            $op:binRelOp
            $subExpr2:expr_without_if) =>
            return expr.binaryRelOperation
              (← binRelOp.toType op)
              (← expr.toType_without_if subExpr1 signatureRelationNames)
              (← expr.toType_without_if subExpr2 signatureRelationNames)

        | `(expr_without_if |
            $subExpr1:expr_without_if
            $dj:dotjoin
            $subExpr2:expr_without_if) =>
            return expr.dotjoin
              (← dotjoin.toType dj)
              (← expr.toType_without_if subExpr1 signatureRelationNames)
              (← expr.toType_without_if subExpr2 signatureRelationNames)

        | `(expr_without_if |
            $op:unRelOp
            $subExpr: expr_without_if) =>
            return expr.unaryRelOperation
              (← unRelOp.toType op)
              (← expr.toType_without_if subExpr signatureRelationNames)

        | `(expr_without_if | -- Hack to allow dotjoin before ()
          $subExpr1:expr_without_if .( $subExpr2:expr_without_if )) =>
          return expr.dotjoin
            dotjoin.dot_join
            (← expr.toType_without_if subExpr1 signatureRelationNames)
            (← expr.toType_without_if subExpr2 signatureRelationNames)

        | `(expr_without_if | -- Hack to allow dotjoin after and before ()
          $subExpr1:expr_without_if .( $subExpr2:expr_without_if ). $subExpr3:expr_without_if) =>
          return expr.dotjoin
            dotjoin.dot_join
            (← expr.toType_without_if subExpr1 signatureRelationNames)
            (expr.dotjoin
              dotjoin.dot_join
              (← expr.toType_without_if subExpr2 signatureRelationNames)
              (← expr.toType_without_if subExpr3 signatureRelationNames))

        | `(expr_without_if | @$name:ident) =>
            return expr.string_rb name.getId.toString

        | syntx =>
            throw s!"No match implemented in \
            Mutuals/toType/expr.toType_without_if \
            for '{syntx}'"


  /--
  Parses an expr syntax to an expr data strucutre
  -/
  partial def expr.toType
    (e : Expression)
    (signatureRelationNames : List String := [])
    : Except String expr := do
      match e with
        | `(expr | ( $e:expr )) =>
          return ← expr.toType e signatureRelationNames

        | `(expr | ( $e:expr_without_if )) =>
          return ← expr.toType_without_if e signatureRelationNames

        | `(expr | $e:expr_without_if) =>
          return ← expr.toType_without_if e signatureRelationNames

        | `(expr |
          if
          $f:formula
          $_:expr_if_connector
          $expr1:expr
          else
          $expr2:expr) =>
          return expr.ifElse
            (← formula.toType f)
            (← expr.toType expr1 signatureRelationNames)
            (← expr.toType expr2 signatureRelationNames)

        | syntx =>
            throw s!"No match implemented in \
            Mutuals/toType/expr.toType \
            for '{syntx}'"

    /--
    Parses an formula syntax to an formula data strucutre
    -/
    partial def formula.toType
    (f : Formula)
    (signatureFactSigNames : List String := [])
    : Except String formula := do
      match f with
        | `(formula | ( $f:formula )) =>
          return ← formula.toType f

        | `(formula | $name:ident) =>
          return formula.string name.getId.toString

        | `(formula | $predName:ident [$predargs,*]) =>
          let mut arguments_typed := []
          for argument in predargs.getElems do
            arguments_typed := arguments_typed.concat
              (← expr.toType argument signatureFactSigNames)

          return formula.pred_with_args
            predName.getId.toString
            arguments_typed

        | `(formula | $op:unRelBoolOp $expression:expr ) =>
          return formula.unaryRelBoolOperation
            (← unRelBoolOp.toType op)
            (← expr.toType expression signatureFactSigNames)

        | `(formula | $op:unLogOp $f:formula ) =>
          return formula.unaryLogicOperation
            (← unLogOp.toType op)
            (← formula.toType f)

        | `(formula | $form1:formula $op:binLogOp $form2:formula) =>
          return formula.binaryLogicOperation
            (← binLogOp.toType op)
            (← formula.toType form1)
            (← formula.toType form2)

        | `(formula |
            $algExpr1:algExpr
            $compOp:algCompareOp
            $algExpr2:algExpr) =>
          return formula.algebraicComparisonOperation
            (← algCompareOp.toType compOp)
            (← algExpr.toType algExpr1)
            (← algExpr.toType algExpr2)

        | `(formula|
            $expr1:expr_without_if
            $op:relCompareOp
            $expr2:expr_without_if) =>
          return formula.relationComarisonOperation
            (← relCompareOp.toType op)
            (← expr.toType_without_if expr1 signatureFactSigNames)
            (← expr.toType_without_if expr2 signatureFactSigNames)

        | `(formula|
            $q:quant
            disj
            $names:ident,* :
            $typeExpression:typeExpr |
            $form:formula
            ) =>
          return formula.quantification
            (← quant.toType q)
            true
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            ([← formula.toType form])

        | `(formula|
            $q:quant
            disj
            $names:ident,* :
            $typeExpression:typeExpr |
            { $form:formula* }
            ) =>

          let mut forms_typed := []
          for f in form do
            forms_typed := forms_typed.concat (← formula.toType f)

          return formula.quantification
            (← quant.toType q)
            true
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            forms_typed

        | `(formula|
            $q:quant
            $names:ident,* :
            $typeExpression:typeExpr |
            $form:formula
            ) =>
          return formula.quantification
            (← quant.toType q)
            false
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            ([← formula.toType form])

        | `(formula|
            $q:quant
            $names:ident,* :
            $typeExpression:typeExpr |
            {$form:formula*}
            ) =>
          let mut forms_typed := []
          for f in form do
            forms_typed := forms_typed.concat (← formula.toType f)
          return formula.quantification
            (← quant.toType q)
            false
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            forms_typed

        -- let declaration
        | `(formula | $alloy_let_decl:alloyLetDecl) =>
          match alloy_let_decl with
            | `(alloyLetDecl | let $name:ident = $value:formula | $body:formula) =>
              return formula.letDeclaration
                (name := name.getId)
                (value := ← formula.toType value)
                (body := [← formula.toType body])
            | `(alloyLetDecl |
                let $name:ident = $value:formula |
                { $body:formula* }
              ) =>

              let mut body_typed := []
              for f in body do
                body_typed := body_typed.concat (← formula.toType f)

              return formula.letDeclaration
                (name := name.getId)
                (value := ← formula.toType value)
                (body := body_typed)
            | syntx => throw s!"No match implemented in \
              Mutuals/toType/formula.toType (let match) \
              for '{syntx}'"

        | `(formula |
          if
          $form1:formula
          $_:formula_if_connector
          $form2:formula
          else
          $form3:formula) =>
          return formula.tertiaryLogicOperation terLogOp.ifelse
              (← formula.toType form1)
              (← formula.toType form2)
              (← formula.toType form3)

        | syntx => throw s!"No match implemented in \
              Mutuals/toType/formula.toType \
              for '{syntx}'"

    /--
    Parses an algExpr syntax to an algExpr data strucutre
    -/
    partial def algExpr.toType
      (ae : AlgExpr)
      : Except String algExpr := do
        match ae with
          | `(algExpr| $number:num) =>
            return algExpr.number (number.getNat : Int)

          | `(algExpr| # $e:expr) =>
            return (algExpr.cardExpression (← expr.toType e))

          | `(algExpr|
              $op:unAlgOp
              $algExpr1:algExpr) =>
            return algExpr.unaryAlgebraOperation
              (← unAlgOp.toType op)
              (← algExpr.toType algExpr1)

          | `(algExpr|
              $op:binAlgOp
              [$algExpr1:algExpr,
              $algExpr2:algExpr]) =>
            return algExpr.binaryAlgebraOperation
              (← binAlgOp.toType op)
              (← algExpr.toType algExpr1)
              (← algExpr.toType algExpr2)

          | syntx => throw s!"No match implemented in \
              Mutuals/toType/algExpr.toType \
              for '{syntx}'"

    /--
    Parses an typeExpr syntax to an typeExpr data strucutre
    -/
    partial def typeExpr.toType
      (te : TypeExpr)
      : Except String typeExpr := do
        match te with
          | `(typeExpr | $e:expr) =>
            return typeExpr.relExpr (← expr.toType e)

          | `(typeExpr | $m:mult $e:expr) =>
            return typeExpr.multExpr (← mult.toType m) (← expr.toType e)

          | `(typeExpr | $arrowExpr:arrowOp) =>
            return typeExpr.arrowExpr (← arrowOp.toType arrowExpr)

          | syntx =>
            throw s!"No match implemented in \
            Mutuals/toType/typeExpr.toType \
            for '{syntx}'"

    /--
    Parses an arrowOp syntax to an arrowOp data strucutre
    -/
    partial def arrowOp.toType
      (op : ArrowOp)
      : Except String arrowOp := do
        match op with
          -- multArrowOpExpr
          | `(arrowOp| ($ae:arrowOp)) => return ← arrowOp.toType ae
          -- multArrowOpExpr
          | `(arrowOp|
              $subArrowExpr1:expr
              $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
              $subArrowExpr2:expr) =>
            return arrowOp.multArrowOpExpr
              (← expr.toType subArrowExpr1)
              (← mult.fromOption mult1)
              (← mult.fromOption mult2)
              (← expr.toType subArrowExpr2)

          -- multArrowOpExprLeft
          | `(arrowOp|
              $subArrowExpr1:expr
              $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
              $subArrowExpr2:arrowOp) =>
            return arrowOp.multArrowOpExprLeft
              (← expr.toType subArrowExpr1)
              (← mult.fromOption mult1)
              (← mult.fromOption mult2)
              (← arrowOp.toType subArrowExpr2)

          --multArrowOpExprRight
          | `(arrowOp|
              $subArrowExpr1:arrowOp
              $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
              $subArrowExpr2:expr) =>
            return arrowOp.multArrowOpExprRight
              (← arrowOp.toType subArrowExpr1)
              (← mult.fromOption mult1)
              (← mult.fromOption mult2)
              (← expr.toType subArrowExpr2)

          --multArrowOp
          | `(arrowOp|
              $subArrowExpr1:arrowOp
              $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
              $subArrowExpr2:arrowOp) =>
            return arrowOp.multArrowOp
              (← arrowOp.toType subArrowExpr1)
              (← mult.fromOption mult1)
              (← mult.fromOption mult2)
              (← arrowOp.toType subArrowExpr2)

          | syntx =>
              throw s!"No match implemented in \
              Mutuals/toType/arrowOp.toType \
              for '{syntx}'"
  end
end Shared
