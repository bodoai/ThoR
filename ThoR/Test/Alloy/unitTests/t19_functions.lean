/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

#alloy funTest
sig a {}
pred pt {
  some a
}
fun ft : a {
  a + a
}
end

#create funTest
#check funTest.functions.ft
#print funTest.functions.ft

#alloy funTest2
sig a {}
sig b {}
fun ft [x : b] : a {
  b + a
}
end

#create funTest2
#check funTest2.functions.ft
#print funTest2.functions.ft
