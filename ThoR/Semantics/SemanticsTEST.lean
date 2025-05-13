import ThoR.Semantics.Semantics
import ThoR.Relation.ElabCallMacro

open ThoR ThoR.Semantics

namespace  predtest

  /-
  sig a {}
  sig b {}
  -/
  class  vars
    (  ThoR_TupleSet  :  Type  )
    [  ThoR.TupleSet  ThoR_TupleSet  ]  where
      (  this_φ_a  :  Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set) )
      (  this_φ_b  :  Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set) )

  end  predtest

  alias  predtest.vars.a  :=  predtest.vars.this_φ_a

  alias  predtest.vars.b  :=  predtest.vars.this_φ_b

  namespace  predtest.preds

  variable
    {  ThoR_TupleSet  :  Type  }
    [  ThoR.TupleSet  ThoR_TupleSet  ]
    [  predtest.vars  ThoR_TupleSet  ]

-- @[default_instance]
-- instance : ThoR.TupleSet ThoR_TupleSet := by sorry

-- @[default_instance]
-- instance : vars ThoR_TupleSet := by sorry

  /-
  create a predicate
  pred p1 {
    a in b
  }
  -/
  def  p1
    {  ThoR_TupleSet  :  Type  }
    [  ThoR.TupleSet  ThoR_TupleSet  ]
    [  predtest.vars  ThoR_TupleSet  ]  :=
      Term.in (R := ThoR_TupleSet)
        (expression1 := Term.rel (  ∻ predtest.vars.this_φ_a))
        (expression2 := Term.rel (  ∻ predtest.vars.this_φ_a))


  /-
  call another predicate
  pred p2 {
    p1
  }
  -/
  def  p2
    {  ThoR_TupleSet  :  Type  }
    [  ThoR.TupleSet  ThoR_TupleSet  ]
    [  predtest.vars  ThoR_TupleSet  ]  :=
      ∻ p1

end  predtest.preds
