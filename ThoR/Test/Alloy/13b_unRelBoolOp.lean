/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy unary relation bool operator

<unRelBoolOp> ::= some
| lone
| one
| no

-/

alloy unRelBoolOpSome
sig a {}
fact {some a}
end

#check unRelBoolOpSome.facts.f0

alloy unRelBoolOpLone
sig a {}
fact {lone a}
end

#check unRelBoolOpLone.facts.f0

alloy unRelBoolOpOne
sig a {}
fact {one a}
end

#check unRelBoolOpOne.facts.f0

alloy unRelBoolOpNo
sig a {}
fact {no a}
end

#check unRelBoolOpNo.facts.f0
