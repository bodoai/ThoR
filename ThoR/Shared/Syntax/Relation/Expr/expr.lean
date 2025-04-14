/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Shared.Syntax.Mutuals.mutuals

open Lean

namespace Shared

  /--
  This syntax represents a relation
  -/
  declare_syntax_cat expr
  abbrev Expression := TSyntax `expr
  syntax constant : expr
  syntax ident : expr
  syntax separatedNamespace : expr -- to call opened module entries

  --function call with argument syntax
  syntax ident "[" expr,* "]" : expr

  syntax "(" expr ")" : expr
  syntax:60 expr:60 binRelOp expr:60 : expr

  -- dotjoin has higher precendence
  syntax:70 expr:70 dotjoin expr:70 : expr

  syntax:80 unRelOp expr:80 : expr

  syntax:60 expr ".(" expr ")" : expr -- dotjoin helper syntax
  syntax:60 expr ".(" expr ")" "." expr : expr -- dotjoin helper syntax

-- used to call an expr (function) with implicit parameters explicitly (see string_rb)
  syntax "@" ident : expr
  namespace expr

    /--
    Generates a string representation of the type
    -/
    partial def toString (e : expr) : String :=
      match e with
        | expr.const c => c.toString
        | expr.string s => s
        | expr.function_call_with_args function_name args =>
          s!"{function_name} {args.map fun arg => arg.toString}"
        | expr.callFromOpen sn => sn.toString
        | expr.unaryRelOperation op e => (op.toString) ++ (e.toString)
        | expr.binaryRelOperation op e1 e2 =>
          (e1.toString) ++ (op.toString) ++ (e2.toString)
        | expr.dotjoin dj e1 e2 =>
          s!"{e1.toString}{dj}{e2.toString}"
        | expr.string_rb s => s

    instance : ToString expr where
      toString : expr -> String := fun e => e.toString

    instance : Inhabited expr where
      default := expr.const (constant.none)

  end expr

end Shared
