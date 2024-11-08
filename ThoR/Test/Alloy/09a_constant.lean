/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

/-
This file tests the alloy constant

<constant> ::= none
| univ
| id

-/

alloy noneConst
sig a {
  r : none
}
end

namespace univConst.test
alloy univConst
sig a {
  r : univ
}
end
startTestBlock univConst
#check (r : ∷ a set -> one univ)

end univConst.test

alloy idConst
sig a {
  r : id
}
end
