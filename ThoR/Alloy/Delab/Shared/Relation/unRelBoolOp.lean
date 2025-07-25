-- /-
-- Copyright (c) 2024 RheinMain University of Applied Sciences
-- Released under license as described in the file LICENSE.
-- Authors: s. file CONTRIBUTORS
-- -/

-- import Lean
-- import ThoR.Alloy.Delab.DelaborationService
-- import ThoR.Relation.Set

-- open Lean PrettyPrinter Delaborator SubExpr

-- @[app_unexpander ThoR.SetMultPredicates.no]
-- def unexpSetPredicatesNo : Unexpander
--   | `($_ $param:ident) => do
--     let new_param :=
--       delaborationService.switch_thoR_representation_to_alloy_representation param
--     `($(mkIdent `no) $new_param)

--   | `($_ $param) => do
--     `($(mkIdent `no) $param)

--   | _ => throw Unit.unit

-- @[app_unexpander ThoR.SetMultPredicates.lone]
-- def unexpSetPredicatesLone : Unexpander
--   | `($_ $param:ident) => do
--     let new_param :=
--       delaborationService.switch_thoR_representation_to_alloy_representation param
--     `($(mkIdent `lone) $new_param)

--   | `($_ $param) => do
--     `($(mkIdent `lone) $param)

--   | _ => throw Unit.unit

-- @[app_unexpander ThoR.SetMultPredicates.one]
-- def unexpSetPredicatesOne : Unexpander
--   | `($_ $param:ident) => do
--     let new_param :=
--       delaborationService.switch_thoR_representation_to_alloy_representation param
--     `($(mkIdent `one) $new_param)

--   | `($_ $param) => do
--     `($(mkIdent `one) $param)

--   | _ => throw Unit.unit

-- @[app_unexpander ThoR.SetMultPredicates.some]
-- def unexpSetPredicatesSome : Unexpander
--   | `($_ $param:ident) => do
--     let new_param :=
--       delaborationService.switch_thoR_representation_to_alloy_representation param
--     `($(mkIdent `some) $new_param)

--   | `($_ $param) => do
--     `($(mkIdent `some) $param)

--   | _ => throw Unit.unit
