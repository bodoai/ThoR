/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

#alloy b2
  sig A extends B {
    p1: B,
    p2: B,
    q1: B lone -> some C,
    q2: B set -> one C,
    q3: B -> some C,
    q4: B lone -> C,
    q5: B -> C,
    q6: B lone -> some C,
    r1: B lone -> some C one -> set D,
    r2: B lone -> some C one -> set D
  }
  sig B {}
  sig C {}
  sig D {}

  pred quant_set {
    all x : A | x = x
    all x : lone A | x = x
    all x : one A | x = x
    all x : some A | x = x
    all x : set A | x = x
  }

  pred quant_bin_rel {
    all x : p1 | x = x
    all x : p1 + p2 | x = x
    all x : (A.p1) -> (A.p2) | x = x
    all x : (A.p1) lone -> some (A.p2) | x = x
  }
end
