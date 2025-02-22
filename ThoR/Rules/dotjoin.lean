import ThoR
open ThoR

namespace Rules.dotjoin
  variable {R : Type} [ThoR.TupleSet R]
  lemma add.dist.l {n m : ℕ} {t1 : RelType R (n+1)} {t2 t3 : RelType R (m+1)} (a : Rel t1) (b : Rel t2) (c : Rel t3) :
    a ⋈ (b + c) ≡ (a ⋈ b) + (a ⋈ c) :=
  by sorry
end Rules.dotjoin
