import ThoR.Alloy
import ThoR.Test.Alloy.test_macro
import ThoR.Rules.quant
import ThoR.Rules.dotjoin
import ThoR.Rules.eq

#alloy
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

#create language/grandpa1

open Person
#print language.grandpa1.vars.Person.mother
#print language.grandpa1.facts.f0

startTestBlock language.grandpa1
#check Rules.eq.refl

lemma l1 : ∻ language.grandpa1.asserts.NoSelfGrandpa := by
  unfold NoSelfGrandpa
  apply Rules.no.intro
  apply Rules.some.neg
  apply Rules.all.intro
  intro p
  unfold ThoR.Quantification.Formula.eval
  intro contra
  fact f0 : language.grandpa1.facts.f0
  cases f0 with
  | intro f1 f2 =>
    apply Rules.no.elim at f1
    apply f1
    apply Rules.some.intro
    simp [ThoR.Quantification.Formula.eval] at contra
    -- dsimp [ThoR.HSubset.hSubset] at contra
    -- unfold ThoR.Rel.subset at contra
    -- simp [ThoR.HDotjoin.hDotjoin] at contra
    -- simp [HAdd.hAdd] at contra
    apply Rules.eq.subset p p at contra
    have h : p ≡ p := by apply Rules.eq.refl
    apply contra at h







    rw [Rules.eq.rw (Rules.dotjoin.add.dist.l _ _ _)] at contra







  sorry
