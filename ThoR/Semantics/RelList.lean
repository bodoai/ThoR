/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.Rel

namespace ThoR

-- definition from https://lean-lang.org/documentation/examples/debruijn/
inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)

infix:67 " :: " => HList.cons
notation "[" "]" => HList.nil

def HList.map.{u, v} {α : Type v} {β₁ : α → Type u} {β₂ : α → Type u} (f : {i: α} → (β₁ i) → (β₂ i)) {indices :List α} (l : HList β₁ indices) : HList β₂ indices
:=
    match l with
    | [] => []
    | h :: t => (f h) :: (HList.map f t)

#print List.foldl
--  	(a -> b -> a) -> a -> [b] -> a

def HList.foldl.{u, v} {α : Type v} {β : α → Type u} {γ : Type} {indices :List α} (l : HList β indices) (f : {i: α} → γ → (β i) → γ) (acc : γ) : γ
:=
    match l with
    | [] => acc
    | h :: t => f (HList.foldl t f acc) h


abbrev RelTypeWithArity (R : Type) [TupleSet R] := Sigma (RelType R)
-- abbrev RelTypeWithDepth (R : Type) [TupleSet R] := (Sigma (RelType R)) × ℕ

abbrev RelList (R : Type) [TupleSet R] := HList (λ (type_w_depth : RelTypeWithArity R) => Rel type_w_depth.2)

end ThoR
