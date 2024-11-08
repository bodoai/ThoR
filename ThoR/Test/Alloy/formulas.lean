/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

alloy emptyPred
sig a {}
pred p1 {}
end

#check p1

alloy emptyFact
sig a {}
fact f1 {}
end

#check f1

alloy emptyFactUnnamed
sig a {}
fact {}
end

alloy factFilled
sig a {}
fact f1 {some a}
end

alloy emptyAssert
sig a {}
assert a1 {}
end

alloy predRelCompOp
sig a,b {}
pred p1 {
  a != b
  a = b
  a in b
}
end

alloy predUnLogOp
sig a,b {}
pred p1 {
  not a != b
}
end

alloy predUnRelBoolOpSigs
sig a,b,c,d {}
pred p1 {
  some a
  lone b
  no c
  one d
}
end

alloy bracketsPred
sig a {}
pred a1 {
  (some a)
}
end

alloy predBinLogOp
sig a,b {}
pred p1 {
  (some a) or (some b)
  (some a) || (some b)
  (some a) and (some b)
  (some a) && (some b)
  (some a) <=> (some b)
  (some a) equivalent (some b)
  (some a) => (some b)
  (some a) implies (some b)
}
end

alloy predTerLogOp
sig a,b,c {}
pred p1 {
  if (some a) then (some b) else (some c)
}
end

alloy predAlgComp
sig a {}
pred p1 {
  #a = 0
}
end

alloy filledFact
sig a {}
fact f1 {
  some a
}
end

alloy filledAssert
sig a {}
assert a1 {
  some a
}
end

alloy predParam
sig a {}
pred p1 (x : a) {
  some x
}
end

alloy predChain
sig a {}
pred p1 {}
pred p2 { p1 }
pred p3 {
  p1 or p2
}
end
