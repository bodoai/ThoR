import Lean
open Lean PrettyPrinter Delaborator SubExpr Expr

declare_syntax_cat alloy

syntax char_a := "a"
syntax char_b := "b"
syntax char_c := "c"
syntax char := char_a <|> char_b <|> char_c
syntax chars := char+

declare_syntax_cat relId

syntax chars ("/" chars)* : relId

syntax relId : alloy

-- declare_syntax_cat relOp
-- syntax relId "." relId : relOp
-- syntax relOp : alloy

syntax "all " alloy " : " alloy " | " alloy: alloy
syntax "[Alloy| " alloy "]" : term

inductive AlloyExpr
  | rel     : String → AlloyExpr
  | all     : String → AlloyExpr → AlloyExpr → AlloyExpr
  | dotjoin : AlloyExpr → AlloyExpr → AlloyExpr


macro_rules
  | `([Alloy| $x:relId]) => `(AlloyExpr.rel $(Lean.quote (toString x.raw)))
  | `([Alloy| all $x:alloy : $y:alloy | $z:alloy ]) => `(AlloyExpr.all [Alloy| $x] [Alloy| $y] [Alloy| $z])

instance : Coe Ident (TSyntax `alloy) where
  coe s := ⟨s.raw⟩

@[app_unexpander AlloyExpr.rel]
def unexpandIdent : Unexpander
  | `($_ident $x:str) =>
    let str := x.getString
    let name := mkIdent $ Name.mkSimple str
    `([Alloy| $name])
  | _ => throw ()

-- @[app_unexpander AlloyExpr.all]
-- def unexpandLet : Unexpander
--   | `($_letE $x:str [Alloy| $v:alloy] [Alloy| $b:alloy]) =>
--     let str := x.getString
--     let name := mkIdent $ Name.mkSimple str
--     `([Alloy| all $name : $v | $b])
--   | _ => throw ()


#check [Alloy| a]
#check [Alloy| a/b]
#check [Alloy| a/b/c]
#check [Alloy| all a : b | c]

#check [Alloy|
  all a : b |
    all c : a/b | a/b/c
]
