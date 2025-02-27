/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Shared.Syntax.quant

namespace ThoR
-- all x : A | no y1 : B | no y2 : B | some disj z1, z2, z3 : C | p[y1,x,y2,z1,z3,z2]
--             names=y1    names=y2

-- all x : A | no y1, y2 : B | some disj z1, z2, z3 : C | p[y1,x,y2,z1,z3,z2]
--             names=y1,y2
-- <--- delab --- elab --->

-- all            no, group y1 y2                   some, disj, group
-- fun (x : A) => (fun (y1 : B) => (fun (y2 : B) => (fun (z1 z2 z3 : C) => p[y1,x,y2,z1,z3,z2])))
--                y1,y2 haben den gleichen Typ
--                                    z1,z2,z3 haben den gleichen Typ
-- --- eval --->
-- ∀ (x ∷ one A), ¬ (∃, (y1 y2 ∷ one B), ∃ (z1 z2 z3 ∷ one C), y1≠y2 → y1≠y3 → y2≠y3 → p y1 x y2 z1 z3 z2)
namespace Quantification
mutual
  inductive Formula: Type u → Type (u+1) where
    | prop      : Prop → Formula PUnit
    | var       : {T' T : Type u} → Shared.quant → (T → Formula T') → Formula T
    | group     : Shared.quant → (Group T) → Formula T
    | disj      : Shared.quant → (Group T) → Formula T

  inductive Group: Type u → Type (u+1)  where
    | formula : {T' T : Type u} → Formula T' → Group T
    | var     : (T → Group T) → Group T
end
end Quantification

namespace Quantification
  namespace Formula
    def evalSome (eval : {T : Type u} → Formula T → Prop) (p : T → Formula T') : Prop := (∃ x, eval (p x))
    def evalNo (eval : {T : Type u} → Formula T → Prop) (p : T → Formula T') : Prop := ¬ (evalSome eval p)
    def evalLone (eval : {T : Type u} → Formula T → Prop)  (p : T → Formula T') : Prop := (∀ x y, (eval (p x)) → (eval (p y)) → x=y)
    def evalOne (eval : {T : Type u} → Formula T → Prop) (p : T → Formula T') : Prop := (evalSome eval p) ∧ (evalLone eval p)
    def evalAll (eval : {T : Type u} → Formula T → Prop) (p : T → Formula T') : Prop := (∀ x, eval (p x))

    def evalGroupLone (eval : {T : Type u} → Formula T → Prop) (g : Group T): Prop :=
      match g with
      | Group.formula f => eval f
      | Group.var p =>
        (∀ x y, evalGroupLone eval (p x) → evalGroupLone eval (p y) → x = y)
    def evalGroupSome (eval : {T : Type u} → Formula T → Prop) (g : Group T): Prop :=
      match g with
      | Group.formula f => eval f
      | Group.var p => (∃ x, evalGroupSome eval (p x))
    def evalGroupAll (eval : {T : Type u} → Formula T → Prop) (g : Group T): Prop :=
      match g with
      | Group.formula f => eval f
      | Group.var p => (∀ x, evalGroupAll eval (p x))
    def evalGroupNo (eval : {T : Type u} → Formula T → Prop) (g : Group T): Prop := ¬ (evalGroupSome eval g)
    def evalGroupOne (eval : {T : Type u} → Formula T → Prop) (g : Group T): Prop := (evalGroupSome eval g) ∧ (evalGroupLone eval g)

    def evalDisjAll  {T' : Type u} (eval : {T : Type u} → Formula T → Prop) (g : Group T') (vars : List T') : Prop :=
      match g with
      | Group.formula f => vars.Nodup → (eval f)
      | Group.var p => (∀ x, evalDisjAll eval (p x) (x::vars))
    def evalDisjSome  {T' : Type u} (eval : {T : Type u} → Formula T → Prop) (g : Group T') (vars : List T') : Prop :=
      match g with
      | Group.formula f => vars.Nodup ∧ (eval f)
      | Group.var p => (∃ x, evalDisjSome eval (p x) (x::vars))
    -- TODO Check evalDisjLone, evalDisjNo, evalDisjOne: Stimmt das so?
    def evalDisjLone  {T' : Type u} (eval : {T : Type u} → Formula T → Prop) (g : Group T') (vars : List T') : Prop :=
      match g with
      | Group.formula f => vars.Nodup → (eval f)
      | Group.var p =>
        (∀ x y, evalDisjLone eval (p x) (x::vars) → evalDisjLone eval (p y) (y::vars) → x = y)
    def evalDisjNo  {T' : Type u} (eval : {T : Type u} → Formula T → Prop) (g : Group T') (vars : List T') : Prop :=
      ¬ (evalDisjSome eval g vars)
    def evalDisjOne  {T' : Type u} (eval : {T : Type u} → Formula T → Prop) (g : Group T') (vars : List T') : Prop :=
      (evalDisjSome eval g vars) /\ (evalDisjLone eval g vars)

    def eval : {T : Type u} → Formula T → Prop := fun f =>
      match f with
        | Formula.prop p  => p
        | Formula.var q p =>
          match q with
          | Shared.quant.no => evalNo eval p
          | Shared.quant.lone => evalLone eval p
          | Shared.quant.one => evalOne eval p
          | Shared.quant.some => evalSome eval p
          | Shared.quant.all => evalAll eval p
        | Formula.group q g =>
          match q with
          | Shared.quant.no => ¬ (evalGroupSome eval g)
          | Shared.quant.lone => (evalGroupSome eval g) ∨ (evalGroupOne eval g)
          | Shared.quant.one => evalGroupOne eval g
          | Shared.quant.some => evalGroupSome eval g
          | Shared.quant.all => evalGroupAll eval g
        | Formula.disj q g =>
          match q with
          | Shared.quant.no => evalDisjNo eval g []
          | Shared.quant.lone => evalDisjLone eval g []
          | Shared.quant.one => True
          | Shared.quant.some => evalDisjSome eval g []
          | Shared.quant.all => evalDisjAll eval g []
    decreasing_by repeat admit
  end Formula
end Quantification

instance {T : Type u}: CoeSort (Quantification.Formula T) Prop where
  coe f := Quantification.Formula.eval f
