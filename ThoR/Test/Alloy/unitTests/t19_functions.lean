/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

#alloy funTest
sig a {}
pred pt {
  some a
}
fun ft : a {
  a + a
}
end

namespace  funTest

  class  vars  (  ThoR_TupleSet  :  Type  )  [  ThoR.TupleSet  ThoR_TupleSet  ]  where  (  this_φ_a  :  ∷  set  univ  )

  end  funTest

  alias  funTest.vars.a  :=  funTest.vars.this_φ_a

  namespace  funTest.preds

  variable  {  ThoR_TupleSet  :  Type  }  [  ThoR.TupleSet  ThoR_TupleSet  ]  [  funTest.vars  ThoR_TupleSet  ]

  def  pt  {  ThoR_TupleSet  :  Type  }  [  ThoR.TupleSet  ThoR_TupleSet  ]  [  funTest.vars  ThoR_TupleSet  ]  :=  (  ThoR.SetMultPredicates.some  (  ∻  funTest.vars.this_φ_a  )  )

  end  funTest.preds

  namespace  funTest.functions

  variable  {  ThoR_TupleSet  :  Type  }  [  ThoR.TupleSet  ThoR_TupleSet  ]  [  funTest.vars  ThoR_TupleSet  ]
  #check ThoR.Rel  (  ThoR.RelType.mk.rel  (  @  funTest.vars.this_φ_a  ThoR_TupleSet  _  _  )  )
  #check (HAdd.hAdd ((  ∻  funTest.vars.this_φ_a  ))  ((  ∻  funTest.vars.this_φ_a  )) )
  #check ((  (  ∻ funTest.vars.this_φ_a  ).getType  )  )

  #check @ThoR.Subtype.cast_fun ThoR_TupleSet _ _ _
  #check @ThoR.Subtype.cast_fun  ThoR_TupleSet _ _ _ (HAdd.hAdd ((  ∻  funTest.vars.this_φ_a  ))  ((  ∻  funTest.vars.this_φ_a  )) )  ((  (  ∻ funTest.vars.this_φ_a  ).getType  )  )  (  by

    aesop  )
  #check ThoR.Rel (∻ funTest.vars.this_φ_a).getType

  -- cast (a + a) -> a
  def  ft  {  ThoR_TupleSet  :  Type  }  [  ThoR.TupleSet  ThoR_TupleSet  ]  [  funTest.vars  ThoR_TupleSet  ]  :  (ThoR.Rel  (∻ funTest.vars.this_φ_a).getType)  :=  @ThoR.Subtype.cast_fun  ThoR_TupleSet _ _ _ (HAdd.hAdd ((  ∻  funTest.vars.this_φ_a  ))  ((  ∻  funTest.vars.this_φ_a  )) )  ((  (  ∻ funTest.vars.this_φ_a  ).getType  )  )  (  by

    aesop  )

  end  funTest.functions


--#create funTest
-- #check funTest.functions.ft
-- #print funTest.functions.ft

-- #alloy funTest2
-- sig a {}
-- sig b {}
-- fun ft [x : b] : a + b {
--   b + a
-- }
-- end

-- #create funTest2
-- #check funTest2.functions.ft
-- #print funTest2.functions.ft
