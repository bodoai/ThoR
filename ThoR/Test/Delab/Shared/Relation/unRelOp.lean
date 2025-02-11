/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

alloy trans_close
  sig a {
    r : a
  }
  fact {
    some x : a | x in a.^r
  }
end

create trans_close
#check trans_close.facts.f0
