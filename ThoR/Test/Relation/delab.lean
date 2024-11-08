/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Delab

open ThoR

variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet]

variable (PERSON : ∷ some univ)
#check PERSON


variable (MANN : ∷ PERSON)
#check MANN

variable (FRAU : ∷ PERSON)
#check FRAU

#check 1 = 1 ∧ True
#check (MANN ≡ (MANN + FRAU)) ∧ True

#check MANN ⊂ PERSON

axiom a1 : MANN ⊂ PERSON
#check a1

variable (TIME : ∷ univ)
#check TIME
def pred1 (t t' : ∷ one TIME) := t + t'
def pred2 := ∀ (t : ∷ one TIME), ∃ (t' : ∷ one TIME), t + t' ≡ t' + t
#check pred2

#check pred1

variable (hatVater : ∷ (MANN + FRAU) set → lone MANN)
#check hatVater

variable (hatMutter : ∷ PERSON → lone FRAU)
#check hatMutter

variable (sf1 : ∷ (FRAU ⋈ hatVater) lone → some (MANN <: (MANN ⋈ hatMutter) :> FRAU))
#check sf1

variable (A1 : ∷ MANN → FRAU)
#check A1

variable (A2 : ∷ MANN → lone FRAU)
#check A2

variable (A3 : ∷ MANN lone → lone FRAU)
#check A3

variable (A4 : ∷ MANN lone → FRAU)
#check A4

variable (A5 : ∷ MANN lone → set FRAU some → one MANN)
#check A5

#check PERSON
#check MANN
variable (MANN' : ∷ MANN)
#check MANN'
#check hatVater
#check A4


-- #fail_check MANN + hatVater
variable (r1 : ∷ MANN + FRAU)
#check r1




#check hatVater & hatMutter
#check MANN ⋈ hatVater
#check hatVater
#check HDotjoin.hDotjoin hatVater MANN
variable (r2 : ∷ hatVater & hatVater - hatMutter ++ hatMutter)
#check r2
variable (r3 : ∷ MANN ⋈ hatVater)
#check r3

def p1 := PERSON ≡ MANN ⋈ ^hatVater + FRAU + (~(FRAU ⟶ MANN) ⋈ PERSON)
-- TODO PERSON, MANN etc. nicht auspacken
#check MANN ⋈ ^hatVater -- hat Arität 1
-- MANN ⋈ ^hatVater ∷ univ
-- MANN ⋈ ^hatVater ∷ set PERSON
-- MANN ⋈ ^hatVater ∷ MANN ⋈ ^hatVater
--- unfold 1. MANN -->
-- MANN ⋈ ^hatVater ∷ (set PERSON) ⋈ ^hatVater
--- unfold 1. PERSON -->
-- MANN ⋈ ^hatVater ∷ (set (some univ)) ⋈ ^hatVater
--- unfold 1. hatVater -->
-- MANN ⋈ ^hatVater ∷ (set (some univ)) ⋈ ^(PERSON set → lone MANN)
--- unfold 1. MANN -->
-- MANN ⋈ ^hatVater ∷ (set (some univ)) ⋈ ^(PERSON set → lone (set PERSON))
--- unfold 2. PERSON -->
-- MANN ⋈ ^hatVater ∷ (set (some univ)) ⋈ ^(PERSON set → lone (set (some univ)))
--- simplify (set (some univ)) -->
-- MANN ⋈ ^hatVater ∷ (set univ) ⋈ ^(PERSON set → lone (set univ))
-- a ⊂ A ∧ b ⊂ B → ^(a ⟶ b) ⊂ set A ⟶ B
-- MANN ⋈ ^hatVater ∷ (set univ) ⋈ (set PERSON ⟶ univ)

-- r = hatVater ⋈ FRAU
--> axiom r_axiom1 : r = hatVater ⋈ FRAU
--> r ∷ set univ

-- r ∷ hatVater ⋈ FRAU
-- r :: (PERSON set ⟶ lone MANN) ⋈ FRAU
-- a ∷ set A ∧ b ∷ set B ∧ c ∷ set C ∧ no B & C → no (a m1 ⟶ m2 b) ⋈ c -->
-- r :: none

-- r ∷ hatVater ⋈ FRAU
-- reduce to arity with types -->
-- r : set PERSON

#check p1
theorem t1 : p1 ThoR_TupleSet PERSON MANN FRAU hatVater := by
  unfold p1
  sorry
