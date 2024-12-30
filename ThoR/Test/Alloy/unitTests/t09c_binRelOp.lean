/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

/-
This file tests the alloy bninary relation operation

<binRelOp> ::= &
| +
| -
| ++
| <:
| :>
| .

-/

namespace intersection
alloy intersection
sig a {
  r : a & a
}
end
create intersection

startTestBlock intersection
#check (a.r : ∷ a set → one (a & a))

end intersection

namespace union
alloy union
sig a {
  r : a + a
}
end
create union

startTestBlock union
#check (a.r : ∷ a set → one (a + a))

end union

namespace difference
alloy difference
sig a {
  r : a - a
}
end
create difference

startTestBlock difference
#check (a.r : ∷ a set → one (a - a))

end difference

namespace overwrite
alloy overwrite
sig a {
  r : a ++ a
}
end
create overwrite

startTestBlock overwrite
#check (a.r : ∷ a set → one (a ++ a))

end overwrite

namespace domain_restriction
alloy domain_restriction
sig a {
  r : a <: a
}
end
create domain_restriction

startTestBlock domain_restriction
#check (a.r : ∷ a set → one (a <: a))

end domain_restriction

namespace range_restriction
alloy range_restriction
sig a {
  r : a :> a
}
end
create range_restriction

startTestBlock range_restriction
#check (a.r : ∷ a set → one (a :> a))

end range_restriction

namespace dot_join
alloy dot_join
sig a {
  r : a . a
}
end
create dot_join

startTestBlock dot_join
#check (a.r : ∷ a set → one (a.a))

end dot_join
