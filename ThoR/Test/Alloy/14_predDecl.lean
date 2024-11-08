/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy predicate declaration

pred <name> ([<preArg>,*])
{ <formula>* }

-/

alloy emptyPred
sig a {}
pred b {}
end

#check a
#check b
