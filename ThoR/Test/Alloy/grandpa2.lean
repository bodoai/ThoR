import ThoR
import ThoR.Test.Alloy.test_macro

#alloy grandpa2
--  module grandpa2 ---- Page 86

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

-- // This should not find any counterexample.
-- check NoSelfFather

-- fun grandpas [p: Person] : set Person {
--   let parent = mother + father + father.wife + mother.husband |
--     p.parent.parent & Man
--   }

-- pred ownGrandpa [p: Person] {
--   p in p.grandpas
--   }

-- run ownGrandpa for 4 Person
end

create grandpa2
-- variable  {  ThoR_TupleSet  :  Type  }  [  ThoR.TupleSet  ThoR_TupleSet  ]  [  grandpa2.vars  ThoR_TupleSet  ]

startTestBlock grandpa2

syntax "fact" ident ":" ident : tactic

macro_rules
| `(tactic| fact $nf:ident : $f:ident) => `(tactic| have $nf := ∻ $f)

#check grandpa2.facts.f0

-- Idee: alloy.check grandpa2.asserts.NoSelfFather
-- -> Beweis steht dann in grandpa2.checks.NoSelfFather?
-- -> Beweis steht dann in grandpa2.proofs.NoSelfFather?
theorem NoSelfFather : ∻ grandpa2.asserts.NoSelfFather
:= by
  unfold grandpa2.asserts.NoSelfFather
  -- have f0 := ∻ grandpa2.facts.f0
  fact f0 : grandpa2.facts.f0
  have f0_l := And.left f0
  have f0_r := And.right f0

  sorry

prove NoSelfFather : grandpa2.asserts.NoSelfFather
:= by
  alloy.fact grandpa2.facts.f0
  ...

-- Kompatibilität mit Alloy erhöhen

-- Idee: run, check ignorieren

-- Idee: Lean-Befehl, um eine .als-Datei einzulesen
-- 1. Schritt: .als-Datei parsen -> AST + ST erzeugen
-- 2. Schritt: wie gehabt: create
