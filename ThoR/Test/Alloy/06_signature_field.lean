/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

/-
This file tests the alloy field declaration

<fieldDecl> ::= <name>,+ : <typeExpr>

-/

namespace sigField.test
alloy sigField
sig a {
  r : a
}
end

startTestBlock sigField
  #check (r : ∷ a set → one a)

end sigField.test

namespace sigFields.test
alloy sigFields
sig a {
  r1,r2 : a
}
end

startTestBlock sigFields
  #check (r1 : ∷ a set → one a)
  #check (r2 : ∷ a set → one a)

end sigFields.test

namespace sigFields2.test
alloy sigFields2
sig a {
  r1 : a,
  r2 : a
}
end

startTestBlock sigFields2
  #check (r1 : ∷ a set → one a)
  #check (r2 : ∷ a set → one a)

end sigFields2.test