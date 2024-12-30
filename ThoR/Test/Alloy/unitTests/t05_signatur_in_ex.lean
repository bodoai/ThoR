/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

/-
This file tests the alloy signature in extensions

<sigExtIn> ::= in <name> (+ <name>)*

-/

namespace emptySigInSig.test
  alloy emptySigInSig
    sig a in b {}
    sig b {}
  end
  create emptySigInSig

  open emptySigInSig
  startTestBlock emptySigInSig
    #check (a : ∷ set b)
    #check inheritance_facts.a
    #check (b : ∷ set univ)
    #check inheritance_facts.b

    example :
      (∻ a) ⊂ (∻ b) :=
        by apply inheritance_facts.a

end emptySigInSig.test

namespace emptySigInSigs.test
  alloy emptySigInSigs
    sig a in b + c {}
    sig b,c {}
  end
  create emptySigInSigs

  open emptySigInSigs
  startTestBlock emptySigInSigs
    #check (a : ∷ set (b + c))
    #check inheritance_facts.a
    #check (b : ∷ set univ)
    #check inheritance_facts.b

    example :
      (∻ a) ⊂ (∻ b) :=
        by apply (And.left inheritance_facts.a)
    example :
      (∻ a) ⊂ (∻ c) :=
        by apply (And.right inheritance_facts.a)

end emptySigInSigs.test

namespace emptySigsInSig.test
  alloy emptySigsInSig
    sig a,b in c {}
    sig c {}
  end
  create emptySigsInSig

  open emptySigsInSig
  startTestBlock emptySigsInSig
    #check (a : ∷ set c)
    #check inheritance_facts.a
    #check (b : ∷ set c)
    #check inheritance_facts.b
    #check (c : ∷ set univ)
    #check inheritance_facts.c

    example :
      (∻ a) ⊂ (∻ c) :=
        by apply inheritance_facts.a
    example :
      (∻ b) ⊂ (∻ c) :=
        by apply inheritance_facts.b

end emptySigsInSig.test

namespace emptySigsInSigs.test
  alloy emptySigsInSigs
    sig a,b in c + d {}
    sig c,d {}
  end
  create emptySigsInSigs

  open emptySigsInSigs
  startTestBlock emptySigsInSigs
    #check (a : ∷ set (c+d))
    #check inheritance_facts.a
    #check (b : ∷ set (c+d))
    #check inheritance_facts.b
    #check (c : ∷ set univ)
    #check inheritance_facts.c
    #check (d : ∷ set univ)
    #check inheritance_facts.d

    example :
      (∻ a) ⊂ (∻ c) :=
        by apply And.left inheritance_facts.a
    example :
      (∻ a) ⊂ (∻ d) :=
        by apply And.right inheritance_facts.a
    example :
      (∻ b) ⊂ (∻ c) :=
        by apply And.left inheritance_facts.b
    example :
      (∻ b) ⊂ (∻ d) :=
        by apply And.right inheritance_facts.b

end emptySigsInSigs.test
