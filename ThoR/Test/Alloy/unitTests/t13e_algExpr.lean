/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy algebra expression

<algExpr> ::= <number>
| <cardExpr>
| <binAlgOp>
[<algExpr>, <algExpr>]
| <unAlgOp> <algExpr>

cant test much here since numbers cant stand alone...

-/

alloy numbers
sig a {}
pred b {1 = 1}
end
create numbers

#check b
#print b
