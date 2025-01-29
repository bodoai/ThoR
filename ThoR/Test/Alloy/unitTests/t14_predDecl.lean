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
create emptyPred

#check a
#check b

alloy extendedIdentPred
sig a {}
pred alloy {}
pred def {}
end
create extendedIdentPred

#check extendedIdentPred.preds.alloy
#check extendedIdentPred.preds.def
