/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy cardinal expression

<cardExpr> ::= # <expr>

like numbers a card expr cant stand alone

-/

alloy cardCmp
sig a {}
pred b {#a = #a}
end
create cardCmp

#check b
#print b
