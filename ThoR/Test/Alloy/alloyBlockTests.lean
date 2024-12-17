/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

alloy empty
end

#alloy x
  sig a {}
  fact b {
  }
end

#alloy x2
  sig A {
    r: A
  }
  sig B {
    r: B
  }
  pred p1 {
    all t: A.r | some t
  }
  pred p2 {
    all uu : B | some uu
  }
end

#check x2.vars.B.q

#alloy b2
  sig A extends B{
    r: B
  }
  sig B {}
  pred x (a1, a2 : r) {some B}
  pred xte {
    all t: r | x [t-t, t]
  }
  fact {xte}
end

-- variables (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet] [b2.vars ThoR_TupleSet]
-- def  xte'  :=
--   (  ThoR.Quantification.Formula.var  Shared.quant.all
--     (  fun  (  y  :  ∷  @  b2.vars.r  )  =>  (
--       ThoR.Quantification.Formula.prop  (
--         ThoR.Quantification.Formula.var  Shared.quant.all  (
--             fun  (  t  :  ∷  (@ b2.vars.r  - y))  =>  (
--               ThoR.Quantification.Formula.prop  (
--                 (∻ b2.preds.x) t t
--                 -- (ThoR.mkSupertype _ _ t)
--                 -- (ThoR.mkSupertype _ _ t)
--               )  )  )
--       )
--     )
--   )
--   )


-- TODO: check types in predicate application
-- (∷R expr1) ⊑ (∷R expr2)
-- def isSubtype t1 t2 : bool := t1 = t2
-- isSubtype r univ

open b2.vars
open b2.preds
#print xte
#check b2.vars.A
#check b2.vars.B
#check b2.inheritance_facts.A
#check b2.inheritance_facts.B
#check b2.facts.f0

alloy verwandschaft
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

#check verwandschaft.inheritance_facts.FRAU
#check verwandschaft.inheritance_facts.MANN
#check verwandschaft.inheritance_facts.PERSON
#check verwandschaft.facts.f0

#alloy buch
abstract sig Buch {
  prequel: lone Buch,
  sequel: lone Buch
}

sig Seite {}

pred test {
  lone x : Buch | some y, z : Seite | x.prequel = z.sequel and
    one disj a : Buch | y = z and z = a
}

fact keineDopplungInReihe{
  lone b:Buch | not (b in b.^prequel and b in b.^sequel)
}

pred EntwederPrequelOderSequel{
  lone disj b,t:Buch | no ((b.^prequel) & (b.^sequel))
}

pred WennPrequelDannSequel {
  all b:Buch | one b.prequel => b.prequel.sequel = b
}

pred WennSequelDannPrequel {
  all b:Buch | one b.sequel => b.sequel.prequel = b
  #Buch = plus[3, 3]
}

pred main {
  EntwederPrequelOderSequel
  WennPrequelDannSequel
  WennSequelDannPrequel
}

end

#check buch.vars.Buch
#print buch.preds.WennSequelDannPrequel
#check buch.facts.keineDopplungInReihe
#check buch.vars.Buch_prequel
#print buch.preds.EntwederPrequelOderSequel
open Shared.quant
#print buch.preds.test
