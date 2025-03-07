import ThoR
import ThoR.Rules.subset

open ThoR

namespace Rules.dotjoin
  variable {R : Type} [ThoR.TupleSet R]
  -- lemma add.dist.l {n m : ℕ} {t1 : RelType R (n+1)} {t2 t3 : RelType R (m+1)} (a : Rel t1) (b : Rel t2) (c : Rel t3) :
  --   a ⋈ (b + c) ≡ (a ⋈ b) + (a ⋈ c) :=
  -- by sorry
  lemma add.dist.l {a b c : R} :
    a ⋈ (b + c) = (a ⋈ b) + (a ⋈ c) :=
  by sorry
  lemma add.dist.r {a b c : R} :
    (a + b) ⋈ c = (a ⋈ c) + (b ⋈ c) :=
  by sorry

  lemma subset {n1 n2 : ℕ} {t1 t1' : RelType R (n1 + 1)} {t2 t2' : RelType R (n2 + 1)} {r1 : Rel t1} {r2 : Rel t2} {r1' : Rel t1'} {r2' : Rel t2'}  :
    r1 ⊂ r1' → r2 ⊂ r2' → r1 ⋈ r2 ⊂ r1' ⋈ r2' :=
  by sorry

  lemma subset.l {n1 n2 : ℕ} {t1 t1' : RelType R (n1 + 1)} {t2 : RelType R (n2 + 1)} {r1 : Rel t1} {r2 : Rel t2} {r1' : Rel t1'} :
    r1 ⊂ r1' → r1 ⋈ r2 ⊂ r1' ⋈ r2 :=
  by
    intro h1
    apply subset
    apply h1
    apply Rules.subset.refl

  lemma subset.r {n1 n2 : ℕ} {t1 : RelType R (n1 + 1)} {t2 t2' : RelType R (n2 + 1)} {r1 : Rel t1} {r2 : Rel t2} {r2' : Rel t2'} :
    r2 ⊂ r2' → r1 ⋈ r2 ⊂ r1 ⋈ r2' :=
  by
    intro h1
    apply subset
    apply Rules.subset.refl
    apply h1

  lemma transclos_1 {t : RelType R 2} {r : Rel t} :
    r ⊂ ^ r := by sorry

  lemma transclos_2 {t : RelType R 2} {r : Rel t} :
    (r ⋈ r) ⊂ (^ r) := by sorry
end Rules.dotjoin
