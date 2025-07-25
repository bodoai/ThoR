-- /-
-- Copyright (c) 2024 RheinMain University of Applied Sciences
-- Released under license as described in the file LICENSE.
-- Authors: s. file CONTRIBUTORS
-- -/

-- import Lean

-- open Lean PrettyPrinter Delaborator SubExpr Expr

-- @[app_unexpander LT.lt]
-- def unexpandLt : Unexpander
--   | `($_ $a $b) =>
--     `($a < $b)

--   | _ => throw Unit.unit

-- @[app_unexpander GT.gt]
-- def unexpandGt : Unexpander
--   | `($_ $a $b) =>
--     `($a > $b)

--   | _ => throw Unit.unit

-- @[app_unexpander Eq]
-- def unexpandEq : Unexpander
--   | `($_ $a $b) =>
--     `($a = $b)

--   | _ => throw Unit.unit

-- @[app_unexpander LE.le]
-- def unexpandLe : Unexpander
--   | `($_ $a $b) =>
--     `($a <= $b) -- in alloy it is =< ??

--   | _ => throw Unit.unit

-- @[app_unexpander GE.ge]
-- def unexpandGE : Unexpander
--   | `($_ $a $b) =>
--     `($a >= $b)

--   | _ => throw Unit.unit
