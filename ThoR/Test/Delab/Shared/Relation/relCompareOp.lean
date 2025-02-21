/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

alloy equal
  sig a {
    r : a
  }
  fact {
    not (r = r)
  }
end
create equal

#check equal.facts.f0

alloy nequal
  sig a {
    r : a
  }
  fact {
    not (r != r)
  }
end
create nequal

#check nequal.facts.f0

alloy incp
  sig a {
    r : a
  }
  fact {
    not (r in r)
  }
end
create incp

#check incp.facts.f0
