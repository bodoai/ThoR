/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy binary algebra operations

<algCompareOp> ::= <
| >
| =
| =<
| >=

-/

alloy cmpLt
sig a {}
pred b { 1 < 2 }
end

#check cmpLt.preds.b
#print cmpLt.preds.b

alloy cmpGt
sig a {}
pred b { 2 > 1 }
end

#check cmpGt.preds.b
#print cmpGt.preds.b

alloy cmpEq
sig a {}
pred b { 1 = 1 }
end

#check cmpEq.preds.b
#print cmpEq.preds.b

alloy cmpLeq
sig a {}
pred b { 1 =< 1 }
end

#check cmpLeq.preds.b
#print cmpLeq.preds.b

alloy cmpGeq
sig a {}
pred b { 1 >= 1 }
end

#check cmpGeq.preds.b
#print cmpGeq.preds.b