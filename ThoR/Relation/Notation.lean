/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic

namespace ThoR

/-- The typeclass behind the notation `a & b` -/
class Intersect (α : Type u) where
  /-- `a & b` computes the intersection of `a` and `b`. -/
  intersect : α → α → α
infixl:65 " & "   => Intersect.intersect

/-- The typeclass behind the notation `a ⊂ b` -/
class Subset (α : Type u) where
  /-- `a ⊂ b` -/
  subset : α → α → Prop
infixl:63 " ⊂ "   => Subset.subset

/-- The typeclass for the cardinality predicate. -/
class HasCard (α : Type u) where
  /-- `hadCard s n` is True iff `s` has cardinality `n`. -/
  hasCard : α -> ℕ -> Prop

/-- The typeclass for the only set constant `none`. -/
class SetConstants (α : Type u) extends HasCard α where
  /-- `none` is the empty set. -/
  none : α
notation " ∅ " => SetConstants.none

/-- The typeclass behind the notation `a ⟶ b` -/
class Cartprod (α : Type u) where
  /-- `a ⟶ b` computes the cartesian product of `a` and `b`. -/
  cartprod : α → α → α
infixl:64 " ⟶ " => Cartprod.cartprod

/-- The typeclass behind the notation `a ⋈ b` -/
class Dotjoin (α : Type u) where
  /-- `a ⋈ b` computes the dotjoin of `a` and `b`. -/
  dotjoin : α → α → α
infixl:66 " ⋈ " => Dotjoin.dotjoin
-- infixl:66 " ⬝ " => Dotjoin.dotjoin

/-- The typeclass behind the notation `^a` -/
class Transclos (α : Type u) where
  /-- `^a` computes the transitive closure of `a`. -/
  transclos : α → α
prefix:67 " ^ " => Transclos.transclos

/-- The typeclass behind the notation `*a` -/
class ReflTransclos (α : Type u) where
  /-- `*a` computes the reflexive transitive closure of `a`. -/
  rtransclos : α → α
prefix:67 " * " => ReflTransclos.rtransclos

/-- The typeclass behind the notation `~a` -/
class Transpose (α : Type u) where
  /-- `~a` computes the transposition of `a`. -/
  transpose : α → α
prefix:67 " ~ " => Transpose.transpose

/-- The typeclass behind the notation `a <: b` -/
class DomRestr (α : Type u) where
  /-- `a <: b` computes the domain restriction of `b` to `a`. -/
  domrestr : α → α → α
infixl:66 " <: " => DomRestr.domrestr

/-- The typeclass behind the notation `a :> b` -/
class RangeRestr (α : Type u) where
  /-- `a :> b` computes the range restriction of `a` to `b`. -/
  rangerestr : α → α → α
infixl:66 " :> " => RangeRestr.rangerestr

class HasArity (α : Type u) where
  hasArity : α → ℕ → Prop

class RelConstants (α : Type u) where
  rel₀ : α
  univ : α
  iden : α
notation:1024 " () " => RelConstants.rel₀

class Card (α : Type u) extends HasCard α where
  card : α -> ℕ
  card_consistent: ∀ a : α, hasCard a (card a)
prefix:63 " # " => Card.card

class Arity (α : Type u) extends HasArity α where
  arity : α -> ℕ
  arity_consistent: ∀ a : α, hasArity a (arity a)

/-- The typeclass behind the notation `a ⟶ b` -/
class HCartprod  (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ⟶ b` computes the cartesian product of `a` and `b`. -/
  hCartprod : α → β → γ
infixl:65 " ⟶ "   => HCartprod.hCartprod

/-- The typeclass behind the notation `a ⋈ b` -/
class HDotjoin (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ⋈ b` computes the dotjoin of `a` and `b`. -/
  hDotjoin : α → β → γ
infixl:66 " ⋈ " => HDotjoin.hDotjoin

/-- The typeclass behind the notation `a <: b` -/
class HDomRestr (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a <: b` computes the domain restriction of `b` to `a`. -/
  hDomrestr : α → β → γ
infixl:66 " <: " => HDomRestr.hDomrestr

/-- The typeclass behind the notation `a :> b` -/
class HRangeRestr (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a :> b` computes the range restriction of `a` to `b`. -/
  hRangerestr : α → β → γ
infixl:66 " :> " => HRangeRestr.hRangerestr

/-- The typeclass behind the notation `a ⊂ b` -/
class HSubset  (α : Type u) (β : Type v) where
  /-- `a ⊂ b` -/
  hSubset : α → β → Prop
infixl:65 " ⊂ "   => HSubset.hSubset

/-- The typeclass behind the notation `a & b` -/
class HIntersect  (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a & b` computes the intersection of `a` and `b`. -/
  hIntersect : α → β → γ
infixl:65 " & "   => HIntersect.hIntersect

/-- The typeclass behind the notation `^a` -/
class HTransclos (α : Type u) (β : outParam (Type w)) where
  /-- `^a` computes the transitive closure of `a`. -/
  hTransclos : α → β
prefix:67 " ^ " => HTransclos.hTransclos

/-- The typeclass behind the notation `*a` -/
class HReflTransclos (α : Type u) (β : outParam (Type v)) where
  /-- `*a` computes the reflexive transitive closure of `a`. -/
  hRTransclos : α → β
prefix:67 " * " => HReflTransclos.hRTransclos

/-- The typeclass behind the notation `~a` -/
class HTranspose (α : Type u) (β : outParam (Type v)) where
  /-- `~a` computes the transposition of `a`. -/
  hTranspose : α → β
prefix:67 " ~ " => HTranspose.hTranspose

/-- The typeclass behind the notation `≡` -/
class HEqual (α : Type u) (β : Type v) where
  /-- `a ≡ b` computes the heterogeneous equality of `a` and `b`. -/
  hEqual : α → β → Prop
infixl:50 " ≡ " => HEqual.hEqual

/-- The typeclass behind the notation `≢` -/
class HNEqual (α : Type u) (β : Type v) where
  /-- `a ≢ b` computes the heterogeneous inequality of `a` and `b`. -/
  hNEqual : α → β → Prop
infixl:50 " ≢ " => HNEqual.hNEqual
