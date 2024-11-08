/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy relation comparison operator

<relCompareOp> ::= in
| =
| !=

-/

alloy In
sig a {}
fact {a in a}
end

#check In.facts.f0

alloy Eq
sig a {}
fact {a = a}
end

#check Eq.facts.f0

alloy NEq
sig a {}
fact {a != a}
end

#check NEq.facts.f0
