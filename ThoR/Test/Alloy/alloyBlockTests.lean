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

#create x

#alloy x2
  sig A {
    r: A
  }
  sig B {
    r: B
  }
  pred p1 {
    all t: B | some t + B.r
  }

end

#create x2

~alloy x3
  sig A {
    r: A
  }
  sig B {
    r: B
  }
  pred p1 {
    all t: A | some r
  }

end


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

#create b2

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

#alloy buch
abstract sig Buch {
  prequel: lone Buch,
  sequel: lone Buch
}

sig Seite {}

fact keineDopplungInReihe{
  lone b:Buch | some z:Buch | not (b in b.^prequel and b in b.^sequel) and
    not z in z.prequel
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

#create buch

#check buch.vars.Buch
#print buch.preds.WennSequelDannPrequel
#check buch.facts.keineDopplungInReihe
#check buch.vars.Buch.prequel
#print buch.preds.EntwederPrequelOderSequel
open Shared.quant

#alloy module m1
  sig a {
    r : a
  }
end

#alloy m2/te
  open m1
  sig a {
    r : a
  }
end

#alloy m3
  open m2/te
  sig a {
    r : a
  }

  fact {
    some this/a
    some m2/te/a
    some m1/a
  }

end

#create m3
