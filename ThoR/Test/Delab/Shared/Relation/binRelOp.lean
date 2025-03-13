/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Alloy.Delab

alloy dotjoin_sig_rel
  sig a {
    r : a
  }
  fact {
    some (a.r)
  }
end

create dotjoin_sig_rel

-- some (a . r)
#check dotjoin_sig_rel.facts.f0

alloy dotjoin_rel_rel
  sig a {
    r : a
  }
  fact {
    some (r.r)
  }
end

create dotjoin_rel_rel

-- some (r . r) / some (dotjoin_rel_rel.vars.r . dotjoin_rel_rel.vars.r)
#check dotjoin_rel_rel.facts.f0

alloy union_rel_rel
  sig a {
    r : a
  }
  fact {
    some (r+r)
  }
end
create union_rel_rel

#check union_rel_rel.facts.f0

alloy intersection_rel_rel
  sig a {
    r : a
  }
  fact {
    some (r & r)
  }
end
create intersection_rel_rel

#check intersection_rel_rel.facts.f0

alloy difference_rel_rel
  sig a {
    r : a
  }
  fact {
    some (r - r)
  }
end
create difference_rel_rel

#check difference_rel_rel.facts.f0

alloy overwrite_rel_rel
  sig a {
    r : a
  }
  fact {
    some (r ++ r)
  }
end
create overwrite_rel_rel

#check overwrite_rel_rel.facts.f0

alloy domain_restriction_sig_rel
  sig a {
    r : a
  }
  fact {
    some (a <: r)
  }
end
create domain_restriction_sig_rel

#check domain_restriction_sig_rel.facts.f0

alloy range_restriction_rel_sig
  sig a {
    r : a
  }
  fact {
    some (r :> a)
  }
end
create range_restriction_rel_sig

#check range_restriction_rel_sig.facts.f0

alloy union_rel_rel_with_quantor
  sig A {
    r : A
  }
  fact {
    some a : A | some (a.r)
  }
end
create union_rel_rel_with_quantor

#check union_rel_rel_with_quantor.facts.f0
