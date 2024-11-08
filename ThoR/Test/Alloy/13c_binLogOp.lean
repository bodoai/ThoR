/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy binary logic operator

<binLogOp> ::= ∥
| or
| &&
| and
| <=>
| equivalent
| =>
| implies

-/


alloy Or
sig a {}
fact {(no a) || (no a)}
end

#check Or.facts.f0

alloy OrAlt
sig a {}
fact {(no a) or (no a)}
end

#check OrAlt.facts.f0

alloy And
sig a {}
fact {(no a) && (no a)}
end

#check And.facts.f0

alloy AndAlt
sig a {}
fact {(no a) and (no a)}
end

#check AndAlt.facts.f0

alloy Eqiv
sig a {}
fact {(no a) <=> (no a)}
end

#check Eqiv.facts.f0

alloy EqivAlt
sig a {}
fact {(no a) equivalent (no a)}
end

#check EqivAlt.facts.f0

alloy Implies
sig a {}
fact {(no a) => (no a)}
end

#check Implies.facts.f0

alloy ImpliesAlt
sig a {}
fact {(no a) implies (no a)}
end

#check ImpliesAlt.facts.f0
