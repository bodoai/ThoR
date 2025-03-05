import ThoR.Alloy
import ThoR.Test.Alloy.test_macro
import ThoR.Rules

import ThoR.Alloy.Delab

alloy
module language/grandpa1 ---- Page 84, 85

abstract sig Person {
  father: lone Man,
  mother: lone Woman
  }

sig Man extends Person {
  wife: lone Woman
  }

sig Woman extends Person {
  husband: lone Man
  }

fact {
  no p: Person | p in p.^(mother+father)
  wife = ~husband
  }

assert NoSelfFather {
  no m: Man | m = m.father
  }

check NoSelfFather

pred ownGrandpa [p: Person] {
  p in p. (mother+father) .father
  }

run ownGrandpa for 4 Person

assert NoSelfGrandpa {
  no p: Person | p in p. (mother+father) .father
  }

check NoSelfGrandpa for 4 Person
end

create language/grandpa1

startTestBlock language.grandpa1
open language.grandpa1
#check vars.Person.father
#print this_φ_Person_ξ_mother

lemma l1 : ∻ language.grandpa1.asserts.NoSelfGrandpa := by
  unfold NoSelfGrandpa
  apply Rules.no.intro
  apply Rules.some.neg
  apply Rules.all.intro
  intro p
  unfold ThoR.Quantification.Formula.eval
  intro contra
  unfold ThoR.Quantification.Formula.eval at contra

--  thor_rw [Rules.dotjoin.add.dist.r] at contra

  fact f0 : language.grandpa1.facts.f0
  cases f0 with
  | intro f1 f2 =>
    clear f2
    apply Rules.no.elim at f1
    apply f1
    clear f1
    apply Rules.some.intro p
    have h1 : p ⊂ p ⋈ ((∻ this_φ_Person_ξ_mother + ∻ this_φ_Person_ξ_father) ⋈ (∻ this_φ_Person_ξ_mother + ∻ this_φ_Person_ξ_father)) := by
      apply Rules.subset.trans
      apply contra
      apply Rules.dotjoin.subset.r
      apply Rules.dotjoin.subset.r
      apply Rules.add.subset.l
    unfold ThoR.Quantification.Formula.eval
    apply Rules.subset.trans
    apply h1
    apply Rules.dotjoin.subset.r
    apply Rules.dotjoin.transclos_2

-- TODO
-- this_φ_Person_ξ_mother kann nicht gemischt werden mit /
-- umgewandelt werden in vars.Person.mother
