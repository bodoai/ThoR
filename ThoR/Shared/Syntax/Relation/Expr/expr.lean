/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Shared.Syntax.Mutuals.mutuals

open Lean

namespace Shared

  syntax "(" expr ")" : expr
  syntax "(" expr_without_if ")" : expr_without_if
  syntax "(" expr ")" : expr_without_if
  syntax expr_without_if : expr

  syntax constant : expr_without_if

  syntax ident : expr_without_if

  syntax separatedNamespace : expr_without_if -- to call opened module entries

  /-- function call with argument syntax -/
  syntax ident "[" expr_without_if,* "]" : expr_without_if

  syntax:60 expr_without_if:60 binRelOp expr_without_if:60 : expr_without_if

  -- dotjoin has higher precendence
  syntax:70 expr_without_if:70 dotjoin expr_without_if:70 : expr_without_if

  syntax:80 unRelOp expr_without_if:80 : expr_without_if

  syntax:60 expr_without_if ".(" expr_without_if ")" : expr_without_if -- dotjoin helper syntax

  syntax:60 expr_without_if ".(" expr_without_if ")" "." expr_without_if : expr_without_if -- dotjoin helper syntax

-- used to call an expr (function) with implicit parameters explicitly (see string_rb)
  syntax "@" ident : expr

  declare_syntax_cat expr_if_connector
  syntax "=>" : expr_if_connector

  /-- If else in expression -/
  syntax formula expr_if_connector expr " else " expr : expr

end Shared
