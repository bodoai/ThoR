/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

#alloy funTest
sig a {}
fun ft : a {
  a + a
}
end

#create funTest
#check funTest.functions.ft
#print funTest.functions.ft
