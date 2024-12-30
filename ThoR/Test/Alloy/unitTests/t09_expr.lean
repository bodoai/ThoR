/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

/-
This file tests the alloy expr

<expr> ::= ( <expr> )
| <constant>
| <name>
| <unRelOp> <expr>
| <expr> <binRelOp>
<expr>

only name is testet here

-/

namespace referenceSelf.test
  alloy referenceSelf
  sig a {
    r : a
  }
  end
  create referenceSelf

  startTestBlock referenceSelf
  #check (a : ∷ set univ)
  #check (r : ∷ a set → one a)

end referenceSelf.test

namespace referenceOther.test
  alloy referenceOther
    sig a {
      r : b
    }
    sig b {}
  end
  create referenceOther

  startTestBlock referenceOther
  #check (a : ∷ set univ)
  #check (r : ∷ a set → one b)
  #check (b : ∷ set univ)

end referenceOther.test
