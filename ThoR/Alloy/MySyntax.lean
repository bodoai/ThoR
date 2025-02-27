open Lean

declare_syntax_cat alloy

syntax ident : alloy

syntax "let" ident ":=" alloy "in" alloy : alloy

syntax "[alloy|" alloy "]" : term

inductive alloyExpr
| rel : String → alloyExpr
| all : alloyExpr → alloyExpr → alloyExpr → alloyExpr

macro_rules
  | `([alloy| $x:ident ]) => `(alloyExpr.rel $(Lean.quote (toString x.getId)))
  | `([alloy| let $r1:ident := $r2:alloy in $r3:alloy]) => `(alloyExpr.all $(Lean.quote (toString r1.getId)) [alloy| $r2] [alloy| $r3])

instance : Coe Ident (TSyntax `alloy) where
  coe s := ⟨s.raw⟩

#check [alloy| a ]
#check [alloy| a := b in c]
