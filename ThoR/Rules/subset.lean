import ThoR
open ThoR

namespace Rules.subset
  variable {R : Type} [ThoR.TupleSet R] {n : ℕ}

  lemma refl {t : RelType R n} (r : Rel t) : (r ⊂ r)
  := by
    simp [HSubset.hSubset]
    simp [Rel.subset]
    apply Set.subset_refl

  lemma antisymm {t1 t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : (r1 ⊂ r2) → (r2 ⊂ r1) → (r1 ≡ r2)
  := by sorry

  lemma trans {t1 t2 t3 : RelType R n} {r1 : Rel t1} {r2 : Rel t2} {r3 : Rel t3}: (r1 ⊂ r2) → (r2 ⊂ r3) → (r1 ⊂ r3)
  := by sorry

  -- lemma trans' {t1 t2 t3 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) (r3 : Rel t3): (r1 ⊂ r2) → (r2 ⊂ r3) → (HSubset.hSubset r1 r3)
  -- := by sorry

end Rules.subset
