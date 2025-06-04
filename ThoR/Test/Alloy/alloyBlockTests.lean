/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Relation.SubType
import ThoR.Relation.RelType

import ThoR.Test.Alloy.test_macro

import ThoR.Macros

import ThoR.Alloy.Delab

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
  -- pred p1 {
  --   all t: B | some t + B.r
  -- }

  pred p2 [x : iden] {
    x = (x + x)
  }

end

#create x2
#check x2.vars.A
#check x2.vars.B
#print x2.preds.p2


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

  namespace b2_example
    namespace  b2

    class  vars  (  ThoR_TupleSet  :  Type  )  [  ThoR.TupleSet  ThoR_TupleSet  ]  where  (  this_φ_B  :  ∷  set  univ  )  (  this_φ_A  :  ∷  set  this_φ_B  ) (  this_φ_A_ξ_r  :  ∷  this_φ_A  set  →  one  this_φ_B  )

    end  b2

    alias  b2.vars.B  :=  b2.vars.this_φ_B

    alias  b2.vars.A  :=  b2.vars.this_φ_A

    alias  b2.vars.A.r  :=  b2.vars.this_φ_A_ξ_r

    namespace  b2.preds

    variable  {  ThoR_TupleSet  :  Type  }  [  ThoR.TupleSet  ThoR_TupleSet  ]  [  b2.vars  ThoR_TupleSet  ]

    def  x  (  a1  a2  :  ∷  @  b2.vars.this_φ_A_ξ_r  )  :=  (  ThoR.SetMultPredicates.some  (  ∻  b2.vars.this_φ_B  )  )

    namespace cast_examples
      variable (  r1  :  ∷  @  b2.vars.this_φ_A_ξ_r  )
      variable (  r2  :  ∷  @  b2.vars.this_φ_A_ξ_r  )

      lemma l1 : ThoR.Subtype.subtypeP (r1 - r2).getType r1.getType := by aesop
      #check ThoR.Subtype.cast (r1-r2) r1.getType (by aesop)

      lemma l2 : ThoR.Subtype.subtypeP (r1 - r2).getType (◃∷  @  b2.vars.this_φ_A_ξ_r) := by aesop
      #check ThoR.Subtype.cast (r1-r2) (◃∷  @  b2.vars.this_φ_A_ξ_r) (by aesop)

      lemma l3 : ThoR.Subtype.subtypeP (r1 - r1).getType (◃∷  @  b2.vars.this_φ_A_ξ_r) := by aesop
      #check ThoR.Subtype.cast (r1-r1) (◃∷  @  b2.vars.this_φ_A_ξ_r) (by aesop)

      lemma l4 : ThoR.Subtype.subtypeP r1.getType (r1 + r2).getType := by aesop
      #check ThoR.Subtype.cast r1 (r1 + r2).getType (by aesop)
    end cast_examples

    def  xte  :=
    (  ThoR.Quantification.Formula.var  Shared.quant.all  )
    (  fun  (  t  :  ∷  @  b2.vars.this_φ_A_ξ_r  )  =>
      (  ThoR.Quantification.Formula.prop  (  (  ∻  b2.preds.x  )


      (cast (  HSub.hSub  t  t  ) ∷  @  b2.vars.this_φ_A_ξ_r)


        t  ))
      )

    def  xte'  :=
    (  ThoR.Quantification.Formula.var  Shared.quant.all  )
    (  fun  (  t  :  ∷  @  b2.vars.this_φ_A_ξ_r  )  =>
      (  ThoR.Quantification.Formula.prop  (  (  ∻  b2.preds.x  )


      (ThoR.Subtype.cast (  HSub.hSub  t  t  ) (t.getType) (by aesop))


        t  ))
      )

    def  xte''  :=
    (  ThoR.Quantification.Formula.var  Shared.quant.all  )
    (  fun  (  t  :  ∷  @  b2.vars.this_φ_A_ξ_r  )  =>
      (  ThoR.Quantification.Formula.prop  (  (  ∻  b2.preds.x  )


      (ThoR.Subtype.cast (  HSub.hSub  t  t  ) (◃∷  @  b2.vars.this_φ_A_ξ_r) (by aesop))


        t  ))
      )
    end  b2.preds

    namespace  b2.facts

    variable  {  ThoR_TupleSet  :  Type  }  [  ThoR.TupleSet  ThoR_TupleSet  ]  [  b2.vars  ThoR_TupleSet  ]

    axiom  f0  :  (  ∻  b2.preds.xte  )

    end  b2.facts

    open  b2.vars  b2.preds  b2.facts
  end b2_example

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
#check xte
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

  pred p1 [p : PERSON] {
    p in p.(hatMutter+hatVater).(hatMutter+hatVater).(hatMutter+hatVater).(hatMutter+hatVater).(hatMutter+hatVater).hatVater
    p in (hatMutter+hatVater).(hatMutter+hatVater).(hatMutter+hatVater).(hatMutter+hatVater).(hatMutter+hatVater).hatVater
    p in (hatMutter+hatVater).(hatMutter+hatVater).(hatMutter+hatVater).(hatMutter+hatVater).(hatMutter+hatVater)
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

#create buch

#check buch.vars.Buch
#print buch.preds.WennSequelDannPrequel
#check buch.facts.keineDopplungInReihe
#check buch.vars.Buch.prequel
#print buch.preds.EntwederPrequelOderSequel
open Shared.quant

namespace testrrr
 namespace  rel_test_fs

  class  vars  (  ThoR_TupleSet  :  Type  )  [  ThoR.TupleSet  ThoR_TupleSet  ]  where  (  this_φ_a  :  ∷  set  univ  )

  end  rel_test_fs

  alias  rel_test_fs.vars.a  :=  rel_test_fs.vars.this_φ_a

  namespace  rel_test_fs.preds

  variable  {  ThoR_TupleSet  :  Type  }  [  ThoR.TupleSet  ThoR_TupleSet  ]  [  rel_test_fs.vars  ThoR_TupleSet  ]

  def  p1  {  ThoR_TupleSet  :  Type  }
    [  ThoR.TupleSet  ThoR_TupleSet  ]
    [  rel_test_fs.vars  ThoR_TupleSet  ]  :=
    ( ThoR.Semantics.Formula.some
      ( ThoR.Semantics.Expression.rel
        (  ∻  rel_test_fs.vars.this_φ_a  )
      )
    )

  end rel_test_fs.preds

end testrrr

/-
variable (ThoR_TupleSet : Type)
create_default_thor_tuple_set
create_default_block_vars_tuple_set testrrr.rel_test_fs

#check testrrr.rel_test_fs.preds.p1
#check (testrrr.rel_test_fs.preds.p1 : Prop)
-/

#alloy rel_test_fs
  sig a {}
  pred p1 {
    some a
  }
end

#create rel_test_fs

#check rel_test_fs.preds.p1
#print rel_test_fs.preds.p1
