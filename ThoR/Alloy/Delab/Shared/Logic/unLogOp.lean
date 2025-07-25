-- /-
-- Copyright (c) 2024 RheinMain University of Applied Sciences
-- Released under license as described in the file LICENSE.
-- Authors: s. file CONTRIBUTORS
-- -/

-- import Lean
-- import ThoR.Alloy.Delab.DelaborationService

-- open Lean PrettyPrinter Delaborator SubExpr Expr

-- @[app_unexpander Not]
-- def unexpandNot : Unexpander
--   | `($_ $param:ident) => do
--     let new_param :=
--       delaborationService.switch_thoR_representation_to_alloy_representation param
--     `($(mkIdent `not) $new_param)

--   | `($_ $param) => do
--     `($(mkIdent `not) $param)

--   | _ => throw Unit.unit
