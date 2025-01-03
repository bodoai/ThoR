/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

/-
This file tests the alloy arrow operation

<arrowOp> ::= <arrowOp> [<mult>]
→
[<mult>] <arrowOp>
| <expr> [<mult>]
→
[<mult>] <arrowOp>
| <arrowOp> [<mult>]
→
[<mult>] <expr>
| <expr> [<mult>]
→
[<mult>] <expr>

-/


namespace arrowOps.test
  alloy arrowOps
  sig a {
    r : a -> a
  }
  end
  create arrowOps

  startTestBlock arrowOps
    #check (arrowOps.vars.a.r : ∷ a set → set (a set → set a))
end arrowOps.test

namespace a_set_arrow_a.test
  alloy a_set_arrow_a
  sig a {
    r : a set -> a
  }
  end
  create a_set_arrow_a


  #check a
  #check a.r
  startTestBlock a_set_arrow_a
    #check (a.r : ∷ a set → set (a set → set a))
end a_set_arrow_a.test

namespace a_some_arrow_a.test
  alloy a_some_arrow_a
  sig a {
    r : a some -> a
  }
  end
  create a_some_arrow_a

  startTestBlock a_some_arrow_a
    #check (a.r : ∷ a set → set (a some → set a))
end a_some_arrow_a.test

namespace a_lone_arrow_a.test
  alloy a_lone_arrow_a
  sig a {
    r : a lone -> a
  }
  end
  create a_lone_arrow_a

  startTestBlock a_lone_arrow_a
    #check (a.r : ∷ a set → set (a lone → set a))
end a_lone_arrow_a.test

namespace a_one_arrow_a.test
  alloy a_one_arrow_a
  sig a {
    r : a one -> a
  }
  end
  create a_one_arrow_a

  startTestBlock a_one_arrow_a
    #check (a.r : ∷ a set → set (a one → set a))
end a_one_arrow_a.test

namespace a_arrow_set_a.test
  alloy a_arrow_set_a
  sig a {
    r : a -> set a
  }
  end
  create a_arrow_set_a

  startTestBlock a_arrow_set_a
    #check (a.r : ∷ a set → set (a set → set a))
end a_arrow_set_a.test

namespace a_arrow_some_a.test
  alloy a_arrow_some_a
  sig a {
    r : a -> some a
  }
  end
  create a_arrow_some_a

  startTestBlock a_arrow_some_a
    #check (a.r : ∷ a set → set (a set → some a))
end a_arrow_some_a.test

namespace a_arrow_lone_a.test
  alloy a_arrow_lone_a
  sig a {
    r : a -> lone a
  }
  end
  create a_arrow_lone_a

  startTestBlock a_arrow_lone_a
    #check (a.r : ∷ a set → set (a set → lone a))
end a_arrow_lone_a.test

namespace a_arrow_one_a.test
  alloy a_arrow_one_a
  sig a {
    r : a -> one a
  }
  end
  create a_arrow_one_a

  startTestBlock a_arrow_one_a
    #check (a.r : ∷ a set → set (a set → one a))
end a_arrow_one_a.test

namespace a_set_arrow_set_a.test
  alloy a_set_arrow_set_a
  sig a {
    r : a set -> set a
  }
  end
  create a_set_arrow_set_a

  startTestBlock a_set_arrow_set_a
    #check (a.r : ∷ a set → set (a set → set a))
end a_set_arrow_set_a.test

namespace a_some_arrow_some_a.test
  alloy a_some_arrow_some_a
  sig a {
    r : a some -> some a
  }
  end
  create a_some_arrow_some_a

  startTestBlock a_some_arrow_some_a
    #check (a.r : ∷ a set → set (a some → some a))
end a_some_arrow_some_a.test

namespace a_lone_arrow_lone_a.test
  alloy a_lone_arrow_lone_a
  sig a {
    r : a lone -> lone a
  }
  end
  create a_lone_arrow_lone_a

  startTestBlock a_lone_arrow_lone_a
    #check (a.r : ∷ a set → set (a lone → lone a))
end a_lone_arrow_lone_a.test

namespace a_one_arrow_one_a.test
  alloy a_one_arrow_one_a
  sig a {
    r : a one -> one a
  }
  end
  create a_one_arrow_one_a

  startTestBlock a_one_arrow_one_a
    #check (a.r : ∷ a set → set (a one → one a))
end a_one_arrow_one_a.test

namespace a_set_arrow_some_a.test
  alloy a_set_arrow_some_a
  sig a {
    r : a set -> some a
  }
  end
  create a_set_arrow_some_a

  startTestBlock a_set_arrow_some_a
    #check (a.r : ∷ a set → set (a set → some a))
end a_set_arrow_some_a.test

namespace a_set_arrow_lone_a.test
  alloy a_set_arrow_lone_a
  sig a {
    r : a set -> lone a
  }
  end
  create a_set_arrow_lone_a

  startTestBlock a_set_arrow_lone_a
    #check (a.r : ∷ a set → set (a set → lone a))
end a_set_arrow_lone_a.test

namespace a_set_arrow_one_a.test
  alloy a_set_arrow_one_a
  sig a {
    r : a set -> one a
  }
  end
  create a_set_arrow_one_a

  startTestBlock a_set_arrow_one_a
    #check (a.r : ∷ a set → set (a set → one a))
end a_set_arrow_one_a.test

namespace a_some_arrow_set_a.test
  alloy a_some_arrow_set_a
  sig a {
    r : a some -> set a
  }
  end
  create a_some_arrow_set_a

  startTestBlock a_some_arrow_set_a
    #check (a.r : ∷ a set → set (a some → set a))
end a_some_arrow_set_a.test

namespace a_some_arrow_lone_a.test
  alloy a_some_arrow_lone_a
  sig a {
    r : a some -> lone a
  }
  end
  create a_some_arrow_lone_a

  startTestBlock a_some_arrow_lone_a
    #check (a.r : ∷ a set → set (a some → lone a))
end a_some_arrow_lone_a.test

namespace a_some_arrow_one_a.test
  alloy a_some_arrow_one_a
  sig a {
    r : a some -> one a
  }
  end
  create a_some_arrow_one_a

  startTestBlock a_some_arrow_one_a
    #check (a.r : ∷ a set → set (a some → one a))
end a_some_arrow_one_a.test

namespace a_lone_arrow_set_a.test
  alloy a_lone_arrow_set_a
  sig a {
    r : a lone -> set a
  }
  end
  create a_lone_arrow_set_a

  startTestBlock a_lone_arrow_set_a
    #check (a.r : ∷ a set → set (a lone → set a))
end a_lone_arrow_set_a.test

namespace a_lone_arrow_some_a.test
  alloy a_lone_arrow_some_a
  sig a {
    r : a lone -> some a
  }
  end
  create a_lone_arrow_some_a

  startTestBlock a_lone_arrow_some_a
    #check (a.r : ∷ a set → set (a lone → some a))
end a_lone_arrow_some_a.test

namespace a_lone_arrow_one_a.test
  alloy a_lone_arrow_one_a
  sig a {
    r : a lone -> one a
  }
  end
  create a_lone_arrow_one_a

  startTestBlock a_lone_arrow_one_a
    #check (a.r : ∷ a set → set (a lone → one a))
end a_lone_arrow_one_a.test

namespace a_one_arrow_set_a.test
  alloy a_one_arrow_set_a
  sig a {
    r : a one -> set a
  }
  end
  create a_one_arrow_set_a

  startTestBlock a_one_arrow_set_a
    #check (a.r : ∷ a set → set (a one → set a))
end a_one_arrow_set_a.test

namespace a_one_arrow_some_a.test
  alloy a_one_arrow_some_a
  sig a {
    r : a one -> some a
  }
  end
  create a_one_arrow_some_a

  startTestBlock a_one_arrow_some_a
    #check (a.r : ∷ a set → set (a one → some a))
end a_one_arrow_some_a.test

namespace a_one_arrow_lone_a.test
  alloy a_one_arrow_lone_a
  sig a {
    r : a one -> lone a
  }
  end
  create a_one_arrow_lone_a

  startTestBlock a_one_arrow_lone_a
    #check (a.r : ∷ a set → set (a one → lone a))
end a_one_arrow_lone_a.test

namespace a_arrow_a_arrow_a.test
  alloy a_arrow_a_arrow_a
  sig a {
    r : a -> a -> a
  }
  end
  create a_arrow_a_arrow_a

  startTestBlock a_arrow_a_arrow_a
    #check (a.r : ∷ a set → set (a set → set (a set → set a)))
end a_arrow_a_arrow_a.test
