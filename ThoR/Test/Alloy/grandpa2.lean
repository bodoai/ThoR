import ThoR.Alloy
-- import ThoR.Test.Alloy.test_macro

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

-- #create language/grandpa1

-- open Person
-- #print language.grandpa1.vars.Person.mother
-- #print language.grandpa1.facts.f0

-- startTestBlock language.grandpa1
-- lemma l1 : ∻ language.grandpa1.asserts.NoSelfGrandpa := by
--   unfold NoSelfGrandpa

--   sorry
