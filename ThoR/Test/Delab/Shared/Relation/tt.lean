import ThoR

  namespace  dotjoin_sig_rel

  class  vars  (  ThoR_TupleSet  :  Type  )  [  ThoR.TupleSet  ThoR_TupleSet  ]  where  (  this_φ_a  :  ∷  set  univ  )

  end  dotjoin_sig_rel

  alias  dotjoin_sig_rel.vars.a  :=  dotjoin_sig_rel.vars.this_φ_a

  namespace  dotjoin_sig_rel.facts

  variable  {  ThoR_TupleSet  :  Type  }  [  ThoR.TupleSet  ThoR_TupleSet  ]  [  dotjoin_sig_rel.vars  ThoR_TupleSet  ]

  axiom  f0  :  (  ThoR.SetMultPredicates.some  (ThoR.Rel.constant.univ  ThoR_TupleSet ))

  end  dotjoin_sig_rel.facts

  open  dotjoin_sig_rel.vars  dotjoin_sig_rel.facts


#alloy dotjoin_sig_rel
  sig a {
  }
  fact {
    some (univ)
  }
end

--#create dotjoin_sig_rel

-- some (a . r)
#check dotjoin_sig_rel.facts.f0
