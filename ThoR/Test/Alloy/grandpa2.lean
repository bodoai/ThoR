import ThoR.Alloy
import ThoR.Test.Alloy.test_macro
import ThoR.Rules

-- import ThoR.Alloy.Delab

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

-- #create language/grandpa1

namespace  language.grandpa1

  class  vars  (  ThoR_TupleSet  :  Type  )  [  ThoR.TupleSet  ThoR_TupleSet  ]  where  (  this_φ_Person  :  ∷  set  univ  )  (  this_φ_Man  :  ∷  set  this_φ_Person  )  (  this_φ_Person_ξ_father  :  ∷  this_φ_Person  set  →  lone  this_φ_Man  )  (  this_φ_Woman  :  ∷  set  this_φ_Person  )  (  this_φ_Person_ξ_mother  :  ∷  this_φ_Person  set  →  lone  this_φ_Woman  )  (  this_φ_Man_ξ_wife  :  ∷  this_φ_Man  set  →  lone  this_φ_Woman  )  (  this_φ_Woman_ξ_husband  :  ∷  this_φ_Woman  set  →  lone  this_φ_Man  )

  end  language.grandpa1

axiom ThoR_TupleSet : Type

@[default_instance]
instance : ThoR.TupleSet ThoR_TupleSet := by sorry

@[default_instance]
instance : language.grandpa1.vars ThoR_TupleSet := by sorry

namespace  language.grandpa1.preds

  def  ownGrandpa  (  p  :  ∷  @grandpa1.vars.this_φ_Person  )  :=  (  ThoR.HSubset.hSubset  p  (  ThoR.HDotjoin.hDotjoin  p  (  ThoR.HDotjoin.hDotjoin  (  HAdd.hAdd  (  language.grandpa1.vars.this_φ_Person_ξ_mother  )  (  language.grandpa1.vars.this_φ_Person_ξ_father  )  )  (  language.grandpa1.vars.this_φ_Person_ξ_father  )  )  )  )

  end  language.grandpa1.preds
