/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Alloy.Delab

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

-- TODO After cast has been fixed, the following of definition of `ft` should be flagged erroneous.
~create funTest2
#check funTest2.functions.ft
#print funTest2.functions.ft

#alloy funTest3
sig a {}
sig b {}

fun ft [x : a] : a {
  some a => x + x
  else x
}

pred pt {
  some b + ft[a]
}

pred pt2(x : a) {
  x = a
}

run {}
end
