/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

#alloy verwandschaft
  abstract sig PERSON {
    hatVater: lone MANN,
    hatMutter: lone FRAU
  }

  sig MANN extends PERSON {}
  sig FRAU extends PERSON {}

  fact {
    all p:PERSON | not (p in p.^(hatVater+hatMutter))
    some PERSON
  }

  assert gleicherUrahnFuerAlle {

    one p:PERSON |
      all p':PERSON |
        p != p' implies p in p'.^(hatVater + hatMutter)
    }
end

#create verwandschaft

#check verwandschaft.inheritance_facts.FRAU
#check verwandschaft.inheritance_facts.MANN
#check verwandschaft.inheritance_facts.PERSON
#check verwandschaft.facts.f0

startTestBlock verwandschaft

  lemma l1 : ∻ verwandschaft.asserts.gleicherUrahnFuerAlle := by
    fact f0 : verwandschaft.facts.f0
    sorry
