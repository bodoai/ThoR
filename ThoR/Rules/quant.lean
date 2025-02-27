import ThoR.Relation.Quantification

open ThoR.Quantification


variable {T' T : Type u} {p : T → Formula T'} (x : T)
def q : Formula T' := p x
#check Formula.eval (p x)
#check Formula.eval (Formula.var Shared.quant.all (λ (x : T) => p x))


namespace Rules.all
    lemma intro {T' T : Type u} {p : T → Formula T'}
      (h : ∀ x, (p x)) :
      (Formula.var Shared.quant.all (λ (x : T) => p x))
    := by
      simp [Formula.eval, Formula.evalAll]
      trivial

    lemma elim {T' T : Type u} {p : T → Formula T'}
      (h : Formula.var Shared.quant.all (λ (x : T) => p x)) :
      ∀ x, (p x)
    := by
      simp [Formula.eval, Formula.evalAll] at h
      trivial

end Rules.all

namespace Rules.some
    lemma intro {T' T : Type u} {p : T → Formula T'}
      (w : T) (h : p w) :
      (Formula.var Shared.quant.some (λ (x : T) => p x))
    := by
      simp [Formula.eval, Formula.evalSome]
      apply Exists.intro w h

    lemma elim {T' T : Type u} {p : T → Formula T'}
      (h : Formula.var Shared.quant.some (λ (x : T) => p x)) :
      exists x, p x
    := by
      simp [Formula.eval, Formula.evalSome] at h
      trivial

    lemma neg {T' T : Type u} {p : T → Formula T'}
      (h : Formula.var Shared.quant.all (λ (x : T) => (Formula.prop ¬ (p x)))) :
      (¬ Formula.var Shared.quant.some (λ (x : T) => p x))
    := by
      simp [Formula.eval, Formula.evalSome]
      simp [Formula.eval, Formula.evalAll] at h
      trivial
end Rules.some

namespace Rules.no
    lemma intro {T' T : Type u} {p : T → Formula T'} :
      (¬ (Formula.var Shared.quant.some (λ (x : T) => (p x)))) →
      (Formula.var Shared.quant.no (λ (x : T) => p x))
    := by
      intro h
      simp [Formula.eval, Formula.evalSome] at h
      simp [Formula.eval, Formula.evalNo]
      simp [Formula.eval, Formula.evalSome]
      trivial

    lemma elim {T' T : Type u} {p : T → Formula T'}
      (h : Formula.var Shared.quant.no (λ (x : T) => p x)) :
      (¬ (Formula.var Shared.quant.some (λ (x : T) => (p x))))
    := by
      simp [Formula.eval, Formula.evalSome]
      simp [Formula.eval, Formula.evalNo] at h
      simp [Formula.eval, Formula.evalSome] at h
      trivial

end Rules.no
