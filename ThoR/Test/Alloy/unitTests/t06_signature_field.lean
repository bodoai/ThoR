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
create sigField

startTestBlock sigField
  #check (a.r : ∷ a set → one a)

end sigField.test

namespace sigField_extIdentname.test
alloy sigField_extIdentname
sig a {
  alloy : a
}
end
create sigField_extIdentname

startTestBlock sigField_extIdentname
  #check (a.alloy : ∷ a set → one a)

end sigField_extIdentname.test

namespace sigFields.test
alloy sigFields
sig a {
  r1,r2 : a
}
end
create sigFields

startTestBlock sigFields
  #check (a.r1 : ∷ a set → one a)
  #check (a.r2 : ∷ a set → one a)

end sigFields.test

namespace sigFields2.test
alloy sigFields2
sig a {
  r1 : a,
  r2 : a
}
end
create sigFields2

startTestBlock sigFields2
  #check (a.r1 : ∷ a set → one a)
  #check (a.r2 : ∷ a set → one a)

end sigFields2.test

namespace sigFieldsoverload.test
alloy sigFieldsoverload
sig a {
  r : a
}
sig b {
  r : b
}
end
create sigFieldsoverload

startTestBlock sigFieldsoverload
  #check (a.r : ∷ a set → one a)
  #check (b.r : ∷ b set → one b)

end sigFieldsoverload.test
