/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import Lean.Parser.Term
open Lean Lean.Parser.Command Lean.Parser


variable (pushMissingOnError : Bool) in
/--
see Lean.Parser.Basic.finishCommentBlock
-/
partial def finishCustomCommentBlock (nesting : Nat) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then eoi s
  else
    let curr := input.get' i h
    let i    := input.next' i h
    if curr == '*' then
      if h : input.atEnd i then eoi s
      else
        let curr := input.get' i h
        if curr == '/' then -- "*/" end of comment
          if nesting == 1 then s.next' input i h
          else finishCustomCommentBlock (nesting-1) c (s.next' input i h)
        else
          finishCustomCommentBlock nesting c (s.setPos i)
    else if curr == '/' then
      if h : input.atEnd i then eoi s
      else
        let curr := input.get' i h
        if curr == '*' then finishCustomCommentBlock (nesting+1) c (s.next' input i h)
        else finishCustomCommentBlock nesting c (s.setPos i)
    else finishCustomCommentBlock nesting c (s.setPos i)
where
  eoi s := s.mkUnexpectedError (pushMissing := pushMissingOnError) "unterminated comment"

variable (pushMissingOnError : Bool) in
/--
see Lean.Parser.Basic.finishCommentBlock
-/
partial def finishCustomComment (nesting : Nat) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then eoi s
  else
    let curr := input.get' i h
    let i    := input.next' i h
    if curr == '\n' then
      if h : input.atEnd i then eoi s
      else
        s.next' input i h
    else if curr == '/' then
      if h : input.atEnd i then eoi s
      else
        let curr := input.get' i h
        if curr == '/' then finishCustomComment (nesting+1) c (s.next' input i h)
        else finishCustomComment nesting c (s.setPos i)
    else finishCustomComment nesting c (s.setPos i)
where
  eoi s := s.mkUnexpectedError (pushMissing := pushMissingOnError) "unterminated comment"

/--
see Lean.Parser.Command.CommentBody
-/
def customCommentBody : Parser :=
{ fn := rawFn (finishCustomCommentBlock (pushMissingOnError := true) 1) (trailingWs := true) }

/--
see Lean.Parser.Command.CommentBody
-/
def customComment : Parser :=
{ fn := rawFn (finishCustomComment (pushMissingOnError := true) 1) (trailingWs := true) }

@[combinator_parenthesizer customCommentBody]
def customCommentBody.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter customCommentBody]
def customCommentBody.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer customComment]
def customComment.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter customComment]
def customComment.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

declare_syntax_cat comment
syntax "//" customComment : comment
syntax "/*" customCommentBody : comment
