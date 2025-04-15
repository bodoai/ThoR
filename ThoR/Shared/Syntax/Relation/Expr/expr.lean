/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Shared.Syntax.Mutuals.mutuals

open Lean

namespace Shared

  syntax constant : expr
  syntax ident : expr
  syntax separatedNamespace : expr -- to call opened module entries

  --function call with argument syntax
  syntax ident "[" expr,* "]" : expr

  syntax "(" expr ")" : expr
  syntax:60 expr:60 binRelOp expr:60 : expr

  -- dotjoin has higher precendence
  syntax:70 expr:70 dotjoin expr:70 : expr

  declare_syntax_cat expr_if_connector
  syntax "=>" : expr_if_connector

  /-- If else in expression -/
  syntax formula expr_if_connector expr " else " expr : expr

  syntax:80 unRelOp expr:80 : expr

  syntax:60 expr ".(" expr ")" : expr -- dotjoin helper syntax
  syntax:60 expr ".(" expr ")" "." expr : expr -- dotjoin helper syntax

-- used to call an expr (function) with implicit parameters explicitly (see string_rb)
  syntax "@" ident : expr

end Shared
