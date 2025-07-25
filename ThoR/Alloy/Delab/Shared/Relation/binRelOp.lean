-- /-
-- Copyright (c) 2024 RheinMain University of Applied Sciences
-- Released under license as described in the file LICENSE.
-- Authors: s. file CONTRIBUTORS
-- -/

-- /-
-- This file contains delaboration for all binRelOps, meaning
-- binary operations between relations.

-- Note, that ,the dotjoin is also included, even tho it is
-- defined in its own file in the alloy part (for precedence reasons)
-- -/

-- import Lean
-- import ThoR.Relation.Set
-- import ThoR.Alloy.Delab.DelaborationService

-- open Lean PrettyPrinter Delaborator SubExpr

-- @[app_unexpander ThoR.Dotjoin.dotjoin]
-- def unexpDotjoin : Unexpander
--   | `($_ $a:ident $b:ident) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($new_a . $new_b)

--   | `($_ $a:ident $b) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     `($new_a . $b)

--   | `($_ $a $b:ident) =>
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($a . $new_b)

--   | `($_ $a $b) =>
--     `($a . $b)

--   | _ => throw Unit.unit

-- @[app_unexpander ThoR.HDotjoin.hDotjoin]
-- def unexpHDotjoin : Unexpander
--   | `($_ $a:ident $b:ident) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($new_a . $new_b)

--   | `($_ $a:ident $b) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     `($new_a . $b)

--   | `($_ $a $b:ident) =>
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($a . $new_b)

--   | `($_ $a $b) =>
--     `($a . $b)

--   | _ => throw Unit.unit

-- @[app_unexpander HAdd.hAdd]
-- def unexpHAdd : Unexpander
--   | `($_ $a:ident $b:ident) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($new_a + $new_b)

--   | `($_ $a:ident $b) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     `($new_a + $b)

--   | `($_ $a $b:ident) =>
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($a + $new_b)

--   | `($_ $a $b) =>
--     `($a + $b)

--   | _ => throw Unit.unit

-- @[app_unexpander ThoR.HIntersect.hIntersect]
-- def unexpHIntersect : Unexpander
--   | `($_ $a:ident $b:ident) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($new_a & $new_b)

--   | `($_ $a:ident $b) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     `($new_a & $b)

--   | `($_ $a $b:ident) =>
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($a & $new_b)

--   | `($_ $a $b) =>
--     `($a & $b)

--   | _ => throw Unit.unit

-- @[app_unexpander HSub.hSub]
-- def unexpHSub : Unexpander
--   | `($_ $a:ident $b:ident) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($new_a - $new_b)

--   | `($_ $a:ident $b) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     `($new_a - $b)

--   | `($_ $a $b:ident) =>
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($a - $new_b)

--   | `($_ $a $b) =>
--     `($a - $b)

--   | _ => throw Unit.unit

-- @[app_unexpander HAppend.hAppend]
-- def unexpHAppend : Unexpander
--   | `($_ $a:ident $b:ident) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($new_a ++ $new_b)

--   | `($_ $a:ident $b) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     `($new_a ++ $b)

--   | `($_ $a $b:ident) =>
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($a ++ $new_b)

--   | `($_ $a $b) =>
--     `($a ++ $b)

--   | _ => throw Unit.unit

-- @[app_unexpander ThoR.HDomRestr.hDomrestr]
-- def unexpHDomRestr : Unexpander
--   | `($_ $a:ident $b:ident) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($new_a <: $new_b)

--   | `($_ $a:ident $b) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     `($new_a <: $b)

--   | `($_ $a $b:ident) =>
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($a <: $new_b)

--   | `($_ $a $b) =>
--     `($a <: $b)

--   | _ => throw Unit.unit

-- @[app_unexpander ThoR.HRangeRestr.hRangerestr]
-- def unexpHRangeRestr : Unexpander
--   | `($_ $a:ident $b:ident) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($new_a :> $new_b)

--   | `($_ $a:ident $b) =>
--     let new_a :=
--       delaborationService.switch_thoR_representation_to_alloy_representation a
--     `($new_a :> $b)

--   | `($_ $a $b:ident) =>
--     let new_b :=
--       delaborationService.switch_thoR_representation_to_alloy_representation b
--     `($a :> $new_b)

--   | `($_ $a $b) =>
--     `($a :> $b)

--   | _ => throw Unit.unit
