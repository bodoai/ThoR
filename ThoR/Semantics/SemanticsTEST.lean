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
      (  this_φ_a  :  Rel (RelType.mk.sig R Shared.mult.set) )
      (  this_φ_b  :  Rel (RelType.mk.sig R Shared.mult.set) )

  end  predtest

  alias  predtest.vars.a  :=  predtest.vars.this_φ_a

  alias  predtest.vars.b  :=  predtest.vars.this_φ_b

  namespace  predtest.preds

  variable
    {  ThoR_TupleSet  :  Type  }
    [  ThoR.TupleSet  ThoR_TupleSet  ]
    [  predtest.vars  ThoR_TupleSet  ]

  /-
  pred p1 {
    a in b
  }
  -/
  def  p1
    {  ThoR_TupleSet  :  Type  }
    [  ThoR.TupleSet  ThoR_TupleSet  ]
    [  predtest.vars  ThoR_TupleSet  ]  :=
      Term.in
        (Term.rel (  ∻  predtest.vars.this_φ_a  ))
        (Term.rel (  ∻  predtest.vars.this_φ_a  ))

end  predtest.preds
