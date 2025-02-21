/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

alloy andt
  sig a {
    r : a
  }
  pred p1 {some a + a}
  fact {
    not (p1 and p1)
  }
end
#create andt

#check andt.facts.f0

alloy ort
  sig a {
    r : a
  }
  pred p1 {some a + a}
  fact {
    not (p1 or p1)
  }
end
#create ort

#check ort.facts.f0

alloy ifft
  sig a {
    r : a
  }
  pred p1 {some a + a}
  fact {
    not (p1 <=> p1)
  }
end
#create ifft

#check ifft.facts.f0

alloy implt
  sig a {
    r : a
  }
  pred p1 {some a + a}
  fact {
    not (p1 => p1)
  }
end
#create implt

#check implt.facts.f0
