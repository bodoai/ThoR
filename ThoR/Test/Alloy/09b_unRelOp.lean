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

#check transClose.preds.p
#print transClose.preds.p

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

#check reflexiveClose.preds.p
#print reflexiveClose.preds.p

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

#check transpose.preds.p
#print transpose.preds.p

~alloy transposeFail
sig a {
  r : ~a
}
end
