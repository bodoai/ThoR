/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

namespace ThoR

-- definitions from https://lean-lang.org/documentation/examples/debruijn/
inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)

infix:67 " :: " => HList.cons
notation "[" "]" => HList.nil

inductive Member : α → List α → Type u
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

def HList.get : HList β is → Member i is → β i
  | a::as, .head => a
  | a::as, .tail h => as.get h

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

end ThoR
