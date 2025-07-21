import ThoR.Semantics.Semantics
import ThoR.Relation.ElabCallMacro

open ThoR

variable (I : Type) [ThoR.TupleSet I]
instance : ThoR.TupleSet I := by sorry
variable (t : ThoR.RelType I n)

#check FormulaTerm.pred
          (λ (parameter_vector : (Vector (ThoR.Rel t) 2)) => FormulaTerm.eq
              (expression1 := ExpressionTerm.toExpr (parameter_vector.get 0))
              (expression2 := ExpressionTerm.toExpr (parameter_vector.get 0)) )

#check FormulaTerm.bind
        (FormulaTerm.pred
          (λ (parameter_vector : (Vector (ThoR.Rel t) 2)) => FormulaTerm.eq
              (expression1 := ExpressionTerm.toExpr (parameter_vector.get 0))
              (expression2 := ExpressionTerm.toExpr (parameter_vector.get 0)) )
        )

def  p1
    :=
    (  FormulaTerm.bind
        (  FormulaTerm.pred
          (  fun  (  parameter_vector  : Vector.{0} (ThoR.Rel t) 1)
            =>
            (  FormulaTerm.eq
              (  ExpressionTerm.toExpr  (parameter_vector.get 0)  )
              (  ExpressionTerm.toExpr  (parameter_vector.get 0)  )
            )
          )
        )
      )


  def  p2
    :=
    (  FormulaTerm.bind
        (  FormulaTerm.pred
          (  fun  (  parameter_vector  : Vector.{0} (ThoR.Rel t) 2)
            =>
            (  FormulaTerm.eq
              (  ExpressionTerm.toExpr  (parameter_vector.get 0)  )
              (  ExpressionTerm.toExpr  (parameter_vector.get 1)  )
            )
          )
        )
      )

#check p1 I t

theorem theorem1 : (p1 I t).eval = (p2 I t).eval := by
  unfold p1
  unfold p2
  unfold FormulaTerm.eval
  unfold FormulaTerm.eval
  simp only [quantify_predicate, Vector.get]
  simp
  apply Iff.intro

  repeat sorry

/-
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
        (expression2 := Term.rel (  ∻ predtest.vars.this_φ_b))


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

namespace  predtest.functions

  variable
  {  ThoR_TupleSet  :  Type  }
  [  ThoR.TupleSet  ThoR_TupleSet  ]
  [  predtest.vars  ThoR_TupleSet  ]

  def  f1
    {  ThoR_TupleSet  :  Type  }
    [  ThoR.TupleSet  ThoR_TupleSet  ]
    [  predtest.vars  ThoR_TupleSet  ]
    :  Rel (∻ predtest.vars.this_φ_b).getType  :=
    cast  ( ∻ predtest.vars.this_φ_b  ) predtest.vars.this_φ_b

  end  predtest.functions

  def  predtest.preds.p3
    {  ThoR_TupleSet  :  Type  }
    [  ThoR.TupleSet  ThoR_TupleSet  ]
    [  predtest.vars  ThoR_TupleSet  ]
    :=  (  ∻  predtest.functions.f1  )
-/
