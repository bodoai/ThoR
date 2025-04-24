/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Relation.Expr.expr
import ThoR.Alloy.SymbolTable.VarDecl.varDecl
import ThoR.Alloy.SymbolTable.SymbolTable
import ThoR.Alloy.Config
import ThoR.Alloy.Syntax.AlloyData.alloyData
import ThoR.Alloy.UnhygienicUnfolder
import ThoR.Relation.ElabCallMacro

/- import all dependent functions -/
import ThoR.Shared.Syntax.Mutuals.mutualsService

/- import all independent functions -/
import ThoR.Shared.Syntax.Relation.Expr.exprHelper

open Alloy Config
open Lean

namespace Shared.expr

  /--
  Transforms an expr_without_if to an expr via the
  shortcut of adding parenthesis
  -/
  private def expr_without_if_to_expr
    (e : Expression_without_if)
    : Expression := Unhygienic.run do
      return ← `(expr | ( $e:expr_without_if ))

  /--
  Parses the given syntax to the type
  -/
  partial def toType
    (e : Expression)
    (signatureRelationNames : List String := [])
    : Except String expr := do
      match e with
        | `(expr | ( $e:expr )) =>
          return ← expr.toType e

        | `(expr | ( $e:expr_without_if )) =>
          return ← expr.toType (expr_without_if_to_expr e)

        | `(expr |
            $op:unRelOp
            $subExpr: expr_without_if) =>
            return expr.unaryRelOperation
              (← unRelOp.toType op)
              (← expr.toType subExpr)

        | `(expr |
            $subExpr1:expr_without_if
            $op:binRelOp
            $subExpr2:expr_without_if) =>
            return expr.binaryRelOperation
              (← binRelOp.toType op)
              (← expr.toType subExpr1)
              (← expr.toType subExpr2)

        | `(expr |
            $subExpr1:expr_without_if
            $dj:dotjoin
            $subExpr2:expr_without_if) =>
            return expr.dotjoin
              (← dotjoin.toType dj)
              (← expr.toType subExpr1)
              (← expr.toType subExpr2)

        | `(expr | $const:constant) =>
            return expr.const (← constant.toType const)

        | `(expr | @$name:ident) =>
            return expr.string_rb name.getId.toString

        | `(expr | $sn:separatedNamespace) =>
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

        | `(expr | $name:ident) =>
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
                (← expr.toType subE1)
                (← expr.toType subE2)

        | `(expr |
            $called_function:ident
            [ $arguments:expr_without_if,* ]
          ) =>
          let mut arguments_typed := []
          for argument in arguments.getElems do
            arguments_typed := arguments_typed.concat (← expr.toType argument)

          return expr.function_call_with_args
            called_function.getId.toString
            arguments_typed

        | `(expr | -- Hack to allow dotjoin before ()
          $subExpr1:expr_without_if .( $subExpr2:expr_without_if )) =>
          return expr.dotjoin
            dotjoin.dot_join
            (← expr.toType subExpr1)
            (← expr.toType subExpr2)

        | `(expr |
          $subExpr1:expr_without_if .( $subExpr2:expr_without_if ). $subExpr3:expr_without_if) =>
          return expr.dotjoin
            dotjoin.dot_join
            (← expr.toType subExpr1)
            (expr.dotjoin
              dotjoin.dot_join
              (← expr.toType subExpr2)
              (← expr.toType subExpr3))

        | syntx =>
            throw s!"No match implemented in \
            exprService.toType \
            for '{syntx}'"

end Shared.expr
