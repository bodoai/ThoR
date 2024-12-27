/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy unary algebra operations

<unAlgOp> ::= -

like numbers negations cant stand alone

-/

alloy negNumbersCmp
sig a {}
pred b { -1 = -1 }
end
create negNumbersCmp

#check b
#print b
