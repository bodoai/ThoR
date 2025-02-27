import ThoR
open ThoR

namespace Rules.eq
  variable {R : Type} [ThoR.TupleSet R] {n : ℕ}

  lemma refl {t : RelType R n} (r : Rel t) : (r ≡ r)
  := by simp [HEqual.hEqual]

  lemma symm {t1 t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : (r1 ≡ r2) → (r2 ≡ r2)
  := by simp [HEqual.hEqual]

  lemma trans {t1 t2 t3 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) (r3 : Rel t3): (r1 ≡ r2) → (r2 ≡ r3) → (r1 ≡ r3)
  := by
    simp [HEqual.hEqual]
    intro h1 h2
    rw [h1,h2]

  lemma subset {t1 t2 t1' t2' : RelType R n} (r1' : Rel t1') (r1 : Rel t1) (r2' : Rel t2' )  (r2 : Rel t2) : r1' ⊂ r2' → (r1 ≡ r1') → (r2 ≡ r2') → r1 ⊂ r2
  := by
    simp [HSubset.hSubset, Rel.subset]
    intro h1 h2 h3
    rw [h2, h3]
    trivial

end Rules.eq
