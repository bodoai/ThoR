/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

/-
This file tests the alloy unary logic operator

<unLogOp> ::= not

-/


alloy unRelOpNot
sig a {}
pred p {}
fact {not p}
end
create unRelOpNot

#check f0
