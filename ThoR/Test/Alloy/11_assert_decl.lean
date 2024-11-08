/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy fact declaration

<assertDecl> ::= assert <name> <property>

-/

alloy emptyAssert
sig a {}
assert a1 {}
end

#check emptyAssert.asserts.a1
