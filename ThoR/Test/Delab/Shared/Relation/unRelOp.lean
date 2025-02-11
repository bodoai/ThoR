/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

alloy dotjoin_sig_rel
  sig a {
    r : a
  }
  fact {
    some x : a | x in a.^r
  }
end

create dotjoin_sig_rel
#check dotjoin_sig_rel.facts.f0
