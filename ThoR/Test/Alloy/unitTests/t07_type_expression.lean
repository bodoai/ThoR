/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

/-
This file tests the alloy type expression

<typeExpr> ::= <arrowOp>
| [<mult>] <expr (unary)>

-/

namespace typeExpr.test
alloy typeExpr
sig a {
  r : a
}
end
create typeExpr

startTestBlock typeExpr
  #check (a.r : ∷ a set → one a)

end typeExpr.test

namespace typeExprMult.test
alloy typeExprMult
sig a {
  r : set a
}
end
create typeExprMult

startTestBlock typeExprMult
  #check (a.r : ∷ a set → set a)

end typeExprMult.test

namespace typeExprSome.test
alloy typeExprSome
sig a {
  r : some a
}
end
create typeExprSome

startTestBlock typeExprSome
  #check (a.r : ∷ a set → some a)

end typeExprSome.test

namespace typeExprLone.test
alloy typeExprLone
sig a {
  r : lone a
}
end
create typeExprLone

startTestBlock typeExprLone
  #check (a.r : ∷ a set → lone a)

end typeExprLone.test

namespace typeExprOne.test
alloy typeExprOne
sig a {
  r : one a
}
end
create typeExprOne

startTestBlock typeExprOne
  #check (a.r : ∷ a set → one a)

end typeExprOne.test
