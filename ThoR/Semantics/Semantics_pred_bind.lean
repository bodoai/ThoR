  inductive Ty : Type → Type 1 where
    | formula : {T : Type} → Ty T -- Prop
    | pred : {T : Type} → Ty T

  @[reducible]
  def Ty.eval {T : Type} (ty : Ty T) : Type :=
    match ty with
    | .formula => Prop
    | @Ty.pred T => T → Prop

  inductive Term : {T : Type} → (ty : Ty T) → Type (u+1) where
    | form : Prop → Term .formula
    | pred {T : Type} : (T → Term .formula) → Term (@Ty.pred T)
    | bind {T : Type} : Term (@Ty.pred T) → Term .formula
    | q_group : Term .formula → Term .formula -- wanted constructor

@[reducible]
def Term.eval {T : Type} {ty : Ty T} (t : Term ty) : ty.eval :=
    match t with

    | Term.form f => f

    | .pred f => λ x => (f x).eval

    | .bind t => ∀ x, t.eval x

    | .q_group f => f.eval -- wanted evaluation

#check (@Term.bind Nat _ (@Term.pred Nat _ ( λ y => (@Term.bind Nat _ (@Term.pred Nat _ (λ (x : Nat) => @Term.form Nat (x = y))))))).eval

example : (@Term.bind Nat _ (@Term.pred Nat _ ( λ y => (@Term.bind Nat _ (@Term.pred Nat _ (λ (x : Nat) => @Term.form Nat (x = y))))))).eval ↔ ∀ (x y : Nat), y = x:= by
  dsimp[Term.eval]
  apply Iff.intro
  · intro h x y
    specialize h x y
    apply h
  · intro h x y
    specialize h x y
    apply h
