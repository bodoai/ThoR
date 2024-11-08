/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.Elab

open ThoR

variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet]

variable (PERSON : ∷ some univ)

#check PERSON

variable (MANN : ∷ PERSON)
#check MANN

variable (FRAU : ∷ PERSON)
#check FRAU

variable (hatVater : ∷ PERSON set → lone MANN)
#check hatVater

variable (hatMutter : ∷ PERSON → lone FRAU)
#check hatMutter

variable (A1 : ∷ MANN → FRAU)
#check A1

variable (A2 : ∷ MANN → lone FRAU)
#check A2

variable (A3 : ∷ MANN lone → lone FRAU)
#check A3

variable (A4 : ∷ MANN lone → FRAU)
#check A4

variable (A5 : ∷ MANN lone → FRAU some → one MANN)
#check A5

#check PERSON
#check MANN
#check hatVater
#check A4
