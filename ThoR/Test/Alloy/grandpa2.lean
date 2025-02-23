import ThoR.Alloy
import ThoR.Test.Alloy.test_macro
import ThoR.Rules.quant
import ThoR.Rules.dotjoin
import ThoR.Rules.eq
import Lean
open Lean

#alloy
module language/grandpa1 ---- Page 84, 85

abstract sig Person {
  father: lone Man,
  mother: lone Woman
  }

sig Man extends Person {
  wife: lone Woman
  }

sig Woman extends Person {
  husband: lone Man
  }

fact {
  no p: Person | p in p.^(mother+father)
  wife = ~husband
  }

assert NoSelfFather {
  no m: Man | m = m.father
  }

check NoSelfFather

pred ownGrandpa [p: Person] {
  p in p. (mother+father) .father
  }

run ownGrandpa for 4 Person

assert NoSelfGrandpa {
  no p: Person | p in p. (mother+father) .father
  }

check NoSelfGrandpa for 4 Person
end

#create language/grandpa1

open Person
#print language.grandpa1.vars.Person.mother
#print language.grandpa1.facts.f0

startTestBlock language.grandpa1

syntax:10 (name := toRel_stx_name) " toRel " term : term

def isSubset : TSyntax `term → Bool
  | `($x:term ⊂ $y:term) => true
  | _ => false

-- def convertSubset : TSyntax `term → TSyntax `term
--   | `($x:term ⊂ $y:term) => `((ThoR.Rel.relation $x) ⊂ (ThoR.Rel.relation $y))
--   | `($t:term) => `($t)

partial def toRel' (t : Term) : Term := Unhygienic.run do
  match t with
    | `(($t)) =>
      return toRel' t

    | `($x:ident) =>
      `($(mkIdent ``ThoR.Rel.relation) $x)

    | `($x + $y) =>
      `($(toRel' x) + $(toRel' y))

    | `($x ⋈ $y) =>
      `($(toRel' x) ⋈ $(toRel' y))

    | `($x ⊂ $y) =>
      `($(toRel' x) ⊂ $(toRel' y))

    | _ => return  t

@[macro toRel_stx_name] def toRelImpl : Macro
  | `(toRel $t:term) =>
      `($(toRel' t))
  | _ => Macro.throwUnsupported

variable (p : ∷ @ Person)
variable (m : ∷ @ Man)
variable (w : ∷ @ Woman)
#check p ⋈ father
#check toRel m & w
#check toRel m + w
#check toRel (p ⋈ father)
#check toRel p ⊂ p
#check toRel p + p
#check toRel m + w
#check toRel m + m + w
#check toRel p ⊂ (m + w)
#check toRel (p ⊂ (m + w))
#check toRel p ⊂ (p ⋈ father)
#check toRel p ⊂ (p + m)
#check toRel p ⊂ (p + m)

lemma l1 : ∻ language.grandpa1.asserts.NoSelfGrandpa := by
  unfold NoSelfGrandpa
  apply Rules.no.intro
  apply Rules.some.neg
  apply Rules.all.intro
  intro p

















  unfold ThoR.Quantification.Formula.eval
  intro contra
  simp [ThoR.Quantification.Formula.eval] at contra

  have h1 :
    (p) ⊂ (p) ⋈ (((∻ Person.mother) + (∻ Person.father)) ⋈ ((∻ Person.father)))
    ↔
    (p.relation) ⊂ (p.relation) ⋈ (((∻ Person.mother).relation + (∻ Person.father).relation) ⋈ ((∻ Person.father).relation))
  := by
    dsimp [ThoR.HSubset.hSubset]
    dsimp [ThoR.Rel.subset]
    simp [ThoR.HDotjoin.hDotjoin]
    simp [HAdd.hAdd]

  rw [Rules.dotjoin.add.dist.r] at h1
  apply h1.mp at contra

  have h2 :
    (p) ⊂ (p) ⋈ (((∻ Person.mother) ⋈ ((∻ Person.father))+ (∻ Person.father) ⋈ ((∻ Person.father))))
    ↔
    (p.relation) ⊂ (p.relation) ⋈ (((∻ Person.mother).relation ⋈ ((∻ Person.father).relation)+ (∻ Person.father).relation ⋈ ((∻ Person.father)).relation))
  := by
    dsimp [ThoR.HSubset.hSubset]
    dsimp [ThoR.Rel.subset]
    simp [ThoR.HDotjoin.hDotjoin]
    simp [HAdd.hAdd]

  apply h2.mpr at contra

  fact f0 : language.grandpa1.facts.f0
  sorry
  -- cases f0 with
  -- | intro f1 f2 =>
  --   apply Rules.no.elim at f1
  --   apply f1
  --   apply Rules.some.intro
  --   simp [ThoR.Quantification.Formula.eval] at contra
  --   -- dsimp [ThoR.HSubset.hSubset] at contra
  --   -- unfold ThoR.Rel.subset at contra
  --   -- simp [ThoR.HDotjoin.hDotjoin] at contra
  --   -- simp [HAdd.hAdd] at contra
  --   apply Rules.eq.subset p p at contra
  --   have h : p ≡ p := by apply Rules.eq.refl
  --   apply contra at h
  --   sorry
