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
create Or

#check Or.facts.f0

alloy OrAlt
sig a {}
fact {(no a) or (no a)}
end
create OrAlt

#check OrAlt.facts.f0

alloy And
sig a {}
fact {(no a) && (no a)}
end
create And

#check And.facts.f0

alloy AndAlt
sig a {}
fact {(no a) and (no a)}
end
create AndAlt

#check AndAlt.facts.f0

alloy Eqiv
sig a {}
fact {(no a) <=> (no a)}
end
create Eqiv

#check Eqiv.facts.f0

alloy EqivAlt
sig a {}
fact {(no a) equivalent (no a)}
end
create EqivAlt

#check EqivAlt.facts.f0

alloy Implies
sig a {}
fact {(no a) => (no a)}
end
create Implies

#check Implies.facts.f0

alloy ImpliesAlt
sig a {}
fact {(no a) implies (no a)}
end
create ImpliesAlt

#check ImpliesAlt.facts.f0
