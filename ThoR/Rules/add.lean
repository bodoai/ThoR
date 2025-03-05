import ThoR
import ThoR.Rules.subset

open ThoR

namespace Rules.add
  variable {R : Type} [ThoR.TupleSet R]

  lemma subset.l {n : ℕ} {t1 t2 : RelType R n} {r1 : Rel t1} {r2 : Rel t2} :
    r2 ⊂ (r1 + r2) :=
  by sorry

  lemma subset.r {n : ℕ} {t1 t2 : RelType R n} {r1 : Rel t1} {r2 : Rel t2} :
    r1 ⊂ (r1 + r2) :=
  by sorry
end Rules.add
