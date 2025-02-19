/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

alloy addt
  sig a {}
  fact {
    #a = plus [3,3]
  }
end
#create addt

#check addt.facts.f0

alloy subt
  sig a {}
  fact {
    #a = minus [3,3]
  }
end
#create subt

#check subt.facts.f0

alloy mult
  sig a {}
  fact {
    #a = mul [3,3]
  }
end
#create mult

#check mult.facts.f0

alloy divt
  sig a {}
  fact {
    #a = div [3,3]
  }
end
#create divt

#check divt.facts.f0

alloy remt
  sig a {}
  fact {
    #a = rem [3, 1]
  }
end
-- rem/mod does not seem to work ?
/-
#create remt

#check remt.facts.f0
-/
