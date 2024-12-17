/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Shared.Syntax.constant
import ThoR.Shared.Syntax.Relation.unRelOp
import ThoR.Shared.Syntax.Relation.binRelOp
import ThoR.Shared.Syntax.Relation.dotjoin
import ThoR.Relation.ElabCallMacro
import ThoR.Shared.Syntax.baseType

open Lean

namespace Shared

  /--
  This inductive type represents a relation
  -/
  inductive expr where
    | const : (const: constant) → expr
    | string : (string : String) → expr
    | unaryRelOperation :
        (operator : unRelOp) →
        (expression : expr) →
        expr
    | binaryRelOperation :
        (operator : binRelOp) →
        (expression1 : expr) →
        (expression2 : expr) →
        expr
    | dotjoin :
        (dj : dotjoin) →
        (expression1 : expr) →
        (expression2 : expr) →
        expr
    | string_rb : (string : String) → expr
  deriving Repr

  /--
  This syntax represents a relation
  -/
  declare_syntax_cat expr
  syntax constant : expr
  syntax ident : expr
  syntax "(" expr ")" : expr
  syntax:60 expr:60 binRelOp expr:60 : expr

  -- dotjoin has higher precendence
  syntax:70 expr:70 dotjoin expr:70 : expr

  syntax:80 unRelOp expr:80 : expr

  syntax:60 expr ".(" expr ")" : expr -- dotjoin helper syntax

-- used to call an expr (function) with implicit parameters explicitly (see string_rb)
  syntax "@" ident : expr
  namespace expr

    /--
    compares two exprs and return true if they are equal
    -/
    def compare (e1 e2 : expr) : Bool :=
      match e1, e2 with
        | expr.const c1, expr.const c2 => c1 == c2
        | expr.string s1, expr.string s2 => s1 == s2
        | expr.unaryRelOperation op1 e1, expr.unaryRelOperation op2 e2 =>
          (op1 == op2) && (compare e1 e2)
        | expr.binaryRelOperation op1 e1 e2,
          expr.binaryRelOperation op2 e3 e4 =>
          (op1 == op2) && (compare e1 e3) && (compare e2 e4)
        | expr.string_rb s1, expr.string_rb s2 => s1 == s2
        | _, _ => false

    /--
    Generates a string representation of the type
    -/
    def toString (e : expr) : String :=
      match e with
        | expr.const c => c.toString
        | expr.string s => s
        | expr.unaryRelOperation op e => (op.toString) ++ (e.toString)
        | expr.binaryRelOperation op e1 e2 =>
          (e1.toString) ++ (op.toString) ++ (e2.toString)
        | expr.dotjoin dj e1 e2 =>
          s!"{e1.toString}{dj}{e2.toString}"
        | expr.string_rb s => s

    /--
    changes an expr (and all of its subexprs)
    to a string rb expression (if they are string)
    -/
    def toStringRb (e : expr) : expr :=
      match e with
        | expr.string s => expr.string_rb s
        | expr.binaryRelOperation op e1 e2 =>
          expr.binaryRelOperation op (e1.toStringRb) (e2.toStringRb)
        | expr.unaryRelOperation op e =>
          expr.unaryRelOperation op (e.toStringRb)
        | expr.dotjoin dj e1 e2 =>
          expr.dotjoin dj (e1.toStringRb) (e2.toStringRb)
        | e => e

    instance : ToString expr where
      toString : expr -> String := fun e => e.toString

    instance : BEq expr where
      beq : expr -> expr -> Bool := fun e1 e2 => e1.compare e2

    instance : Inhabited expr where
      default := expr.const (constant.none)

    /--
    Generates a syntax representation of the type
    -/
    def toSyntax
      (blockName : Name)
      (e : expr)
      : TSyntax `expr := Unhygienic.run do
        match e with
          | expr.const c => `(expr| $(c.toSyntax):constant)
          | expr.string s => `(expr| $(mkIdent s.toName):ident)
          | expr.unaryRelOperation op e => `(expr| $(op.toSyntax):unRelOp $(e.toSyntax blockName):expr)
          | expr.binaryRelOperation op e1 e2 =>
            `(expr| $(e1.toSyntax blockName):expr $(op.toSyntax):binRelOp $(e2.toSyntax blockName):expr)
          | expr.dotjoin dj e1 e2 =>
            `(expr|$(e1.toSyntax blockName):expr $(dj.toSyntax):dotjoin $(e2.toSyntax blockName):expr)
          -- FIXME In der folgenden Zeile fehlt noch das $rb -> Macht das Probleme?
          | expr.string_rb s => `(expr| @$(mkIdent s!"{blockName}.vars.{s}".toName):ident)

    /--
    Generates a Lean term corosponding with the type
    -/
    private def toTerm
      (e : expr)
      (inBLock : Bool)
      (blockName : Name)
      (quantorNames : List (String) := []) -- used to know which names must be pure
      : TSyntax `term := Unhygienic.run do
        match e with
          | expr.const c => return (c.toTerm)

          | expr.string s => do
            if inBLock && !(quantorNames.contains s) then
              `((
                ∻ $(mkIdent s!"{blockName}.vars.{s}".toName)
              ))
            else
              `($(mkIdent s.toName))

          | expr.unaryRelOperation op e =>
            `(( $(op.toTerm)
                $(e.toTerm inBLock
                  blockName quantorNames)
              ))

          | expr.binaryRelOperation op e1 e2 =>
            `(( $(op.toTerm)
                $(e1.toTerm inBLock
                  blockName quantorNames
                  )
                $(e2.toTerm inBLock
                  blockName quantorNames
                  )
              ))

          | expr.dotjoin dj e1 e2 =>
            `(( $(dj.toTerm)
                $(e1.toTerm inBLock
                  blockName quantorNames
                  )
                $(e2.toTerm inBLock
                  blockName quantorNames
                  )
              ))

          | expr.string_rb s => do
            `((@$(mkIdent s.toName) $(baseType.getIdent) _ _))

    /--
    Generates a Lean term corosponding with the type from outside an alloy block
    -/
    def toTermOutsideBlock
      (e : expr)
      (quantorNames : List (String) := [])
      :=
        toTerm e false `none quantorNames

    /--
    Generates a Lean term corosponding with the type from inside an alloy block
    -/
    def toTermFromBlock
      (e : expr)
      (blockName : Name)
      (quantorNames : List (String) := []) :=
        toTerm e true blockName quantorNames

    /--
    Parses the given syntax to the type
    -/
    partial def toType
      (e : TSyntax `expr)
      (signatureRelationNames : List String := [])
      : expr :=
        match e with
          | `(expr | ( $e:expr )) => expr.toType e
          | `(expr |
              $op:unRelOp
              $subExpr: expr) =>
              expr.unaryRelOperation
              (unRelOp.toType op)
              (expr.toType subExpr)

          | `(expr |
              $subExpr1:expr
              $op:binRelOp
              $subExpr2:expr) =>
              expr.binaryRelOperation
              (binRelOp.toType op)
              (expr.toType subExpr1)
              (expr.toType subExpr2)

          | `(expr |
              $subExpr1:expr
              $dj:dotjoin
              $subExpr2:expr) =>
              expr.dotjoin
              (dotjoin.toType dj)
              (expr.toType subExpr1)
              (expr.toType subExpr2)

          | `(expr | $const:constant) =>
              expr.const (constant.toType const)

          | `(expr | @$name:ident) => Id.run do
              expr.string_rb name.getId.toString

          | `(expr | $name:ident) => Id.run do
              let parsedName := name.getId

              if parsedName.isAtomic then

                let exprStringName := name.getId.lastComponentAsString

                -- If the string (name) of the expr is a sigField in a sigFact
                if (signatureRelationNames.contains exprStringName) then
                  expr.dotjoin
                    dotjoin.dot_join
                    (expr.string "this")
                    (expr.string exprStringName)

                else
                  expr.string exprStringName

              else -- ident contains . which must be parsed as dotjoin
                let x := (parsedName.splitAt (parsedName.components.length - 1))
                let subExpr1 := x.1
                let subExpr2 := x.2

                let subE1 : TSyntax `expr := Unhygienic.run
                  `(expr| $(mkIdent subExpr1): ident)

                let subE2 : TSyntax `expr := Unhygienic.run
                  `(expr| $(mkIdent subExpr2): ident)

                expr.dotjoin
                  dotjoin.dot_join
                  (expr.toType subE1)
                  (expr.toType subE2)

          | `(expr | -- Hack to allow dotjoin before ()
            $subExpr1:expr .( $subExpr2:expr )) =>
            expr.dotjoin
              dotjoin.dot_join
              (expr.toType subExpr1)
              (expr.toType subExpr2)


          | _ => expr.const constant.none -- unreachable

    /--
    Gets the required variables for the type
    -/
    def getReqVariables
      (e : expr)
      : List (String) :=
        match e with
          | expr.string s => [s]
          | expr.unaryRelOperation _ e => e.getReqVariables
          | expr.binaryRelOperation _ e1 e2 => (e1.getReqVariables) ++ (e2.getReqVariables)
          | expr.dotjoin _ e1 e2 => (e1.getReqVariables) ++ (e2.getReqVariables)
          | _ => []

    def getRelationCalls
      (e : expr)
      (relationNames : List (String))
      : List (String) := Id.run do
        match e with
          | expr.string s =>
            if relationNames.contains s then
              return [s]
            else
              return []

          | expr.unaryRelOperation _ e =>
            e.getRelationCalls relationNames

          | expr.binaryRelOperation _ e1 e2 =>
            (e1.getRelationCalls relationNames) ++
              (e2.getRelationCalls relationNames)

          | expr.dotjoin _ e1 e2 =>
            let e1eval := (e1.getRelationCalls relationNames)
            let e2eval := (e2.getRelationCalls relationNames)
            if (e2eval.length == 1) then
              match e1 with
                | expr.string s =>
                  let e2value := e2eval.get! 0
                  return [s!"{s}.{e2value}"]

                | _ => return e1eval ++ e2eval

            else
              return e1eval ++ e2eval

          | _ => []

    def replaceRelationCalls
      (e: expr)
      (relationNames :List (String))
      (replacementNames :List (String))
      : expr := Id.run do
        match e with
          | expr.string s =>
            let index := relationNames.indexOf s
            if index == relationNames.length then
              e
            else
              expr.string (replacementNames.get! index)

          | expr.binaryRelOperation op e1 e2 =>
            expr.binaryRelOperation
              op
              (e1.replaceRelationCalls relationNames replacementNames)
              (e2.replaceRelationCalls relationNames replacementNames)

          | expr.unaryRelOperation op e =>
            expr.unaryRelOperation
              op
              (e.replaceRelationCalls relationNames replacementNames)

          | expr.dotjoin dj e1 e2 =>
            let namesToCheck := replacementNames.map fun rn => (rn.splitOn "_")
            for index in [0 : (namesToCheck.length)] do
              let name := namesToCheck.get! index
              if
                e1 == (expr.string (name.get! 0)) &&
                e2 == (expr.string (name.get! 1))
              then
                return expr.string (replacementNames.get! index)

            expr.dotjoin
              dj
              (e1.replaceRelationCalls relationNames replacementNames)
              (e2.replaceRelationCalls relationNames replacementNames)

          | _ => default

  end expr



end Shared
