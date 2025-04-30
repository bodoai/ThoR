/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import Lean

import ThoR.Alloy.Syntax.IgnoredSyntax.comment

open Lean Lean.Elab Command Term

namespace Alloy

  declare_syntax_cat syntax_with_comments_element

  syntax str : syntax_with_comments_element
  syntax ident : syntax_with_comments_element

  /--
  A call to syntax_with_comments is like a call to syntax, except
  between every element of the syntax the comment syntax_category is added
  -/
  syntax
    (name := syntax_with_comments_stx)
    ("#")? "syntax_with_comments" (syntax_with_comments_element)* ":" ident : command

  private def evaluate_syntax_creation
  (elements :TSyntaxArray `syntax_with_comments_element)
  (stx_cat : Ident)
  : Command
  := Unhygienic.run do

  let comment_stx ← `(stx | ($(mkIdent `comment):ident)?)

  let mut elements_as_stx : Array (TSyntax `stx) := #[comment_stx]
  for element in elements do
    match element with
      | `(syntax_with_comments_element | $str_element:str) =>
        let str_element_stx ← `(stx | $(str_element):str)
        elements_as_stx := elements_as_stx.push str_element_stx
        elements_as_stx := elements_as_stx.push comment_stx

      | `(syntax_with_comments_element | $ident_element:ident) =>
        let ident_element_stx ← `(stx | $(ident_element):ident)
        elements_as_stx := elements_as_stx.push ident_element_stx
        elements_as_stx := elements_as_stx.push comment_stx

      | _ => unreachable!

  return ← `(command | syntax $[$elements_as_stx]* : $stx_cat)

  @[command_elab syntax_with_comments_stx]
  private def syntax_with_comments_implementation : CommandElab := fun stx => do
    try
      match stx with
        | `(
            # syntax_with_comments
            $elements:syntax_with_comments_element*
            : $stx_cat:ident
          ) =>

          let s := (evaluate_syntax_creation elements stx_cat)
          logInfo s
          elabCommand s

        | `(
            syntax_with_comments
            $elements:syntax_with_comments_element*
            : $stx_cat:ident
          ) =>

          let s := (evaluate_syntax_creation elements stx_cat)
          elabCommand s

        | _ => return
    catch | x => throwError x.toMessageData

end Alloy

syntax
  (name := syntax_match_with_comments_stx)
  ("#")? "syntax_match_with_comments"
  Parser.Term.dynamicQuot : term

@[term_elab syntax_match_with_comments_stx]
private def syntax_match_with_comments_implementation
: TermElab := fun stx expectedType? => do
    match stx with
      | `(
          # syntax_match_with_comments
          $syntax_match_quote:dynamicQuot
        ) =>

        /-
        --let snk : TSyntax `ident := `a

        let q ←  `(Parser.Term.quot | `(x))
        let qq ←  `(Parser.Term.dynamicQuot | `(term | a))
        --let qqq ←  `(Parser.Term.dynamicQuot | `($snk | a))

        let a ← `(term | `(t))

        let first_element := syntax_match_elements.get! 0
        let mut elements_stx ← `(stx| $first_element:ident)
        for element in syntax_match_elements.toList.drop 1 do
          elements_stx :=
            (← `(stx| $element:ident))

        let syntax_quot ←
          Lean.Elab.Term.Quotation.mkSyntaxQuotation
            elements_stx
            syntax_match_name.getId


         let syntax_quot ←
          Lean.Elab.Term.Quotation.mkSyntaxQuotation
            elements_stx
            syntax_match_name.getId
        -/

        logInfo syntax_match_quote

        elabTerm
          syntax_match_quote
          expectedType?

      | `(
            syntax_match_with_comments
            $syntax_match_quote:dynamicQuot
        ) =>

        /-
        let first_element := syntax_match_elements.get! 0
        let mut elements_stx ← `(stx| $first_element:ident)
        for element in syntax_match_elements.toList.drop 1 do
          elements_stx :=
            (← `(stx| $element:ident))

        let syntax_quot ←
          Lean.Elab.Term.Quotation.mkSyntaxQuotation
            elements_stx
            syntax_match_name.getId
        -/

        elabTerm
          syntax_match_quote
          expectedType?

      | syntx =>
        throwError s!"Could not create Syntax match for syntax '{syntx}'"

declare_syntax_cat example_stx_cat
#syntax_with_comments  "example_stx"  : example_stx_cat

#check (# syntax_match_with_comments `(example_stx_cat | example_stx ))

def canMatch (i : TSyntax `example_stx_cat) : Bool :=
  match i with
    | `(example_stx_cat | $[$_:comment]? example_stx $[$_:comment]?) => true
    | _ => false

def zz : Bool := Unhygienic.run do
  let try1 ← `(example_stx_cat | /*kek*/ example_stx)
  return canMatch try1

#eval zz
