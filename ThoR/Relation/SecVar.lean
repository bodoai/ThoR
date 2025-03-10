axiom T : Type

class axiom_preds :=
  axiom1 : ∀ t:T, t = t
  axiom2 : ∀ t: T, t ≠ t

@[default_instance]
instance : axiom_preds := by sorry

open axiom_preds
#print axiom1

theorem nonsens : 1=2 := by
  have h := axiom1






section Example
  variable (a : ℕ)
  def p := a = a

  theorem t1: p a := by
    unfold p
    rfl

  theorem t1_fail: p := by
    unfold p
    rfl
end Example
