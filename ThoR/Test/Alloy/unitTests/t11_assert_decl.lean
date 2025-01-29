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
create emptyAssert

#check emptyAssert.asserts.a1

alloy emptyAssert_extIdentName
sig a {}
assert alloy {}
end
create emptyAssert_extIdentName

#check emptyAssert_extIdentName.asserts.alloy
