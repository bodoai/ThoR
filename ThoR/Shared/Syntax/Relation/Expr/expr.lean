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
import ThoR.Shared.Syntax.Relation.relationSeparator
import ThoR.Alloy.Syntax.Signature.signatureSeparator
import ThoR.Alloy.Syntax.SeparatedNamespace

open Lean

namespace Shared

  /--
  This inductive type represents a relation
  -/
  inductive expr where
    | const : (const: constant) → expr
    | string : (string : String) → expr
    | callFromOpen : (calledEntry : Alloy.separatedNamespace) → expr
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
  syntax separatedNamespace : expr -- to call opened module entries
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
        | expr.callFromOpen sn1, expr.callFromOpen sn2 => sn1 == sn2
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
        | expr.callFromOpen sn => sn.toString
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
          | expr.callFromOpen sn => `(expr| $(sn.toSyntax):separatedNamespace)
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

          | expr.callFromOpen sn =>
            let snt := sn.representedNamespace.getId.toString
            if inBLock then
              `((
                ∻ $(mkIdent s!"{blockName}.vars.{snt}".toName)
              ))
            else
              return sn.toTerm

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

          | `(expr | $sn:separatedNamespace) =>
            expr.callFromOpen (Alloy.separatedNamespace.toType sn)

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
          | expr.callFromOpen sn => Id.run do
            -- this String can be something like m1.A
            let sns := sn.representedNamespace.getId.lastComponentAsString
            let snsSplit := sns.splitOn "."
            if snsSplit.isEmpty then
              return [sns]
            else
              [snsSplit.getLast!]
          | expr.unaryRelOperation _ e => e.getReqVariables
          | expr.binaryRelOperation _ e1 e2 => (e1.getReqVariables) ++ (e2.getReqVariables)
          | expr.dotjoin _ e1 e2 => (e1.getReqVariables) ++ (e2.getReqVariables)
          | _ => []

    def getStringExpr (e:expr) : String :=
      match e with
        | expr.string s => s
        | _ => default

    /--
    returns all signatures that are called and also are in the
    given name list (signature names).

    note that giving the names is required, since you can't decide
    on syntax alone if something is a signature or a relation
    -/
    def getSignatureCalls
      (e : expr)
      (signatureNames : List (String))
      (moduleName : String := default)
      : List (String) := Id.run do
        match e with
          | expr.string s =>
            if signatureNames.contains s then [s] else []

          | expr.callFromOpen sn =>
            let sns := sn.representedNamespace.getId.lastComponentAsString
            let snsSplit := sns.splitOn "."
            if snsSplit.isEmpty then
              if signatureNames.contains sns then [sns] else []
            else
              if signatureNames.contains snsSplit.getLast! then
                if (moduleName != default) && (snsSplit.get! 0) == "this" then
                  [s!"{moduleName}.{snsSplit.getLast!}"]
                else
                  [sns]
              else
                []

          | expr.unaryRelOperation _ e =>
            e.getSignatureCalls signatureNames

          | expr.binaryRelOperation _ e1 e2 =>
            (e1.getSignatureCalls signatureNames) ++
              (e2.getSignatureCalls signatureNames)

          | expr.dotjoin _ e1 e2 =>
            (e1.getSignatureCalls signatureNames) ++
              (e2.getSignatureCalls signatureNames)

          | _ => [] -- unreachable

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

          | expr.callFromOpen sn =>
            let sns := sn.representedNamespace.getId.lastComponentAsString
            let snsSplit := sns.splitOn "."
            if snsSplit.isEmpty then
              if relationNames.contains sns then [sns] else []
            else
              if relationNames.contains snsSplit.getLast! then [sns] else []

          | expr.unaryRelOperation _ e =>
            e.getRelationCalls relationNames

          | expr.binaryRelOperation _ e1 e2 =>
            (e1.getRelationCalls relationNames) ++
              (e2.getRelationCalls relationNames)

          | expr.dotjoin _ e1 e2 =>
            let e1eval := (e1.getRelationCalls relationNames)
            let e2eval := (e2.getRelationCalls relationNames)
            if (e1eval.length == 0) && (e2eval.length == 1) then
              match e1 with
                | expr.string s =>
                  let e2value := e2eval.get! 0
                  return [s!"{s}.{e2value}"]

                | _ => return e1eval ++ e2eval

            else
              return e1eval ++ e2eval

          | _ => []

  end expr

end Shared
