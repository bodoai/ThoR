/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy binary algebra operations

<binAlgOp> ::= plus
| minus
| div
| mul
| rem

like numbers the resulting algExpr cant stand alone

-/

alloy plusNumbers
sig a {}
pred b { plus[1,1] = 2 }
end
create plusNumbers
#check b
#print b

alloy minusNumbers
sig a {}
pred b { minus[1,1] = 0 }
end
create minusNumbers
#check minusNumbers.preds.b
#print minusNumbers.preds.b

alloy divNumbers
sig a {}
pred b { div[4,2] = 2 }
end
create divNumbers

#check divNumbers.preds.b
#print divNumbers.preds.b

alloy mulNumbers
sig a {}
pred b { mul[2,2] = 4 }
end
create mulNumbers

#check mulNumbers.preds.b
#print mulNumbers.preds.b

alloy remNumbers
sig a {}
pred b { rem[5,2] = 1 }
end
create remNumbers

#check remNumbers.preds.b
#print remNumbers.preds.b
