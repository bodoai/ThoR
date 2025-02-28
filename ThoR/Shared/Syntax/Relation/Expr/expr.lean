/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Shared.Syntax.Constant.constantService
import ThoR.Shared.Syntax.Relation.unRelOp
import ThoR.Shared.Syntax.Relation.binRelOp
import ThoR.Shared.Syntax.Relation.dotjoin
import ThoR.Relation.ElabCallMacro
import ThoR.Alloy.Config
import ThoR.Alloy.Syntax.SeparatedNamespace

open Lean Config

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
  syntax separatedNamespace : expr -- to call opened module entries
  syntax ident : expr
  syntax constant : expr
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

    instance : ToString expr where
      toString : expr -> String := fun e => e.toString

    instance : BEq expr where
      beq : expr -> expr -> Bool := fun e1 e2 => e1.compare e2

    instance : Inhabited expr where
      default := expr.const (constant.none)

  end expr

end Shared
