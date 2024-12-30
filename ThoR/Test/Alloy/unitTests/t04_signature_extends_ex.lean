/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

/-
This file tests the alloy signature extends extensions

<sigExtExtends> ::= extends <name>

-/

namespace emptySigExtendsSig.test
  alloy emptySigExtendsSig
    sig a extends b {}
    sig b {}
  end
  create emptySigExtendsSig
  startTestBlock emptySigExtendsSig
    #check (a : ∷ set b)
    #check emptySigExtendsSig.inheritance_facts.a
    #check (b : ∷ set univ)
    #check emptySigExtendsSig.inheritance_facts.b
    example :
      (∻ a) ⊂ (∻ b) :=
        by apply emptySigExtendsSig.inheritance_facts.a

end emptySigExtendsSig.test

namespace emptySigExtendsSigs.test
  alloy emptySigExtendsSigs
    sig a extends b {}
    sig b extends c {}
    sig c {}
  end
  create emptySigExtendsSigs
  startTestBlock emptySigExtendsSigs
    #check (a : ∷ set b)
    #check emptySigExtendsSigs.inheritance_facts.a
    #check (b : ∷ set c)
    #check emptySigExtendsSigs.inheritance_facts.b
    #check (c : ∷ set univ)
    #check emptySigExtendsSigs.inheritance_facts.c

    example :
      (∻ a) ⊂ (∻ b) :=
        by apply (And.left emptySigExtendsSigs.inheritance_facts.b)

    example :
      (∻ b) ⊂ (∻ c) :=
        by apply (And.right emptySigExtendsSigs.inheritance_facts.b)

end emptySigExtendsSigs.test

namespace emptySigsExtendsSig.test
  alloy emptySigsExtendsSig
    sig a,b extends c {}
    sig c {}
  end
  create emptySigsExtendsSig

  startTestBlock emptySigsExtendsSig
    #check (a : ∷ set c)
    #check emptySigsExtendsSig.inheritance_facts.a
    #check (b : ∷ set c)
    #check emptySigsExtendsSig.inheritance_facts.b
    #check (c : ∷ set univ)
    #check emptySigsExtendsSig.inheritance_facts.c

    example :
    (∻ a) ⊂ (∻ c) :=
      by apply (And.right emptySigsExtendsSig.inheritance_facts.a)

    example :
      (∻ b) ⊂ (∻ c) :=
        by apply (And.right emptySigsExtendsSig.inheritance_facts.b)

end emptySigsExtendsSig.test

namespace emptySigsExtendsSigs.test
  alloy emptySigsExtendsSigs
    sig a,b extends c {}
    sig c extends d{}
    sig d {}
  end
  create emptySigsExtendsSigs

  startTestBlock emptySigsExtendsSigs
    #check a
    #check (a : ∷ set c)
    #check emptySigsExtendsSigs.inheritance_facts.a
    #check (b : ∷ set c)
    #check emptySigsExtendsSigs.inheritance_facts.b
    #check (c : ∷ set d)
    #check emptySigsExtendsSigs.inheritance_facts.c
    #check (d : ∷ set univ)
    #check emptySigsExtendsSigs.inheritance_facts.d

    example :
    (∻ c) ⊂ (∻ d) :=
      by apply (And.right emptySigsExtendsSigs.inheritance_facts.c)

end emptySigsExtendsSigs.test

namespace emptySigsExtendsAbstractSig.test
  alloy emptySigsExtendsAbstractSig
    sig a extends c {}
    sig b extends c {}
    abstract sig c {}
  end
  create emptySigsExtendsAbstractSig

  startTestBlock emptySigsExtendsAbstractSig
    #check a
    #check (a : ∷ set c)
    #check emptySigsExtendsAbstractSig.inheritance_facts.a
    #check (b : ∷ set c)
    #check emptySigsExtendsAbstractSig.inheritance_facts.b
    #check (c : ∷ set univ)
    #check emptySigsExtendsAbstractSig.inheritance_facts.c

    open emptySigsExtendsAbstractSig
    example :
    ((∻ c) ≡ (∻ a) + (∻ b))
    ∧
    ((∻ a) ⊂ (∻ c))
    ∧
    ((∻ b) ⊂ (∻ c))
  := by
    apply And.intro
    · try apply And.left (And.left inheritance_facts.c);
    · apply And.intro
      · apply And.right (And.left inheritance_facts.c)
      · apply And.right inheritance_facts.c

end emptySigsExtendsAbstractSig.test
