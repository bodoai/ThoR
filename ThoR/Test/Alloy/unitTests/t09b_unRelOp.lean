/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy unary relation operation

<unRelOp> ::= ∧
| *
| ∼

-/

alloy transClose
sig a {
  r : a
}
pred p {
  some x : r | x in ^r
}
end
create transClose

#check transClose.preds.p
#print transClose.preds.p


--single transclose not allowed in Alloy
~alloy transCloseFail
sig a {
  r : ^a
}
end


alloy reflexiveClose
sig a {
  r : a
}
pred p {
  some x : r | x in *r
}
end
create reflexiveClose

#check reflexiveClose.preds.p
#print reflexiveClose.preds.p


--single reflexiveClose not allowed in Alloy
~alloy reflexiveCloseFail
sig a {
  r : *a
}
end


alloy transpose
sig a {
  r : a
}
pred p {
  some x : r | ~x in r
}
end
create transpose

#check transpose.preds.p
#print transpose.preds.p


--single transclose not allowed in Alloy
~alloy transposeFail
sig a {
  r : ~a
}
end
