/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

alloy uNot
  sig a {
    r : a
  }
  fact {
    not (r = r)
  }
end
create uNot

#check uNot.facts.f0
