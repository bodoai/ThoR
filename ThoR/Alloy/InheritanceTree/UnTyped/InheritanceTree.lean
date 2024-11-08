/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Relation.Set

import ThoR.Alloy.Syntax.AST
import ThoR.Alloy.Syntax.Signature.Inheritance.sigExt
import ThoR.Shared.Syntax.typeExpr

import ThoR.Alloy.InheritanceTree.UnTyped.Node

open Lean Lean.Elab Command Term
open Shared

namespace Alloy

/--
This structure represents the inheritance of signature declarations
as an inheritance tree (IT)
-/
structure InheritanceTree where
  mk :: (nodes : List (Node))
deriving Repr

namespace InheritanceTree

  /--
  Generates an empty IT
  -/
  def emptyTree : InheritanceTree :=
    {nodes := []}

  /--
  Generates a string representation of the IT
  -/
  def toString (it: InheritanceTree) : String :=
    reprStr it

  /--
  Adds a single node to the IT
  -/
  def addNode (it: InheritanceTree) (n: Node) : InheritanceTree :=
    {it with nodes := it.nodes.append [n]}

  /--
  adds a single inChild (a child wich extends by 'in') to the IT
  -/
  def updateNodeInChild (it: InheritanceTree) (name: String) (abs : Bool) (child: String) := Id.run do
    let mut nNodes := it.nodes
    for node in nNodes do
      if node.name == name then
        return {it with nodes := (nNodes.replace node (node.addInChild child))}

    return it.addNode (Node.oneInChildNode name abs child)

  /--
  adds a single inChild (a child wich extends by 'extends') to the IT
  -/
  def updateNodeExChild
    (it: InheritanceTree) (name: String) (abs : Bool)
    (child: String) := Id.run do
    let mut nNodes := it.nodes
    for node in nNodes do
      if node.name == name then
        return {it with nodes := (nNodes.replace node (node.addExChild child))}

    return it.addNode (Node.oneExChildNode name abs child)

  /--
  Gets all children of a signature declaration
  -/
  def getInChildrenOf (it: InheritanceTree) (name: String) := Id.run do
    for node in it.nodes do
      if node.name == name then
        return node.inChildren
    return [] -- unknown Node has no children

  /--
  Gets all children (connected with 'in') of a signature declaration
  -/
  def getExChildrenOf (it: InheritanceTree) (name: String) := Id.run do
    for node in it.nodes do
      if node.name == name then
        return node.exChildren

    return [] -- unknown Node has no children

  /--
  Gets all children (connected with 'extends') of a signature declaration
  -/
  def getChildrenOf (it: InheritanceTree) (name: String) := Id.run do
    for node in it.nodes do
      if node.name == name then
        return node.inChildren ++ node.exChildren

    return [] -- unknown Node has no children

  /--
  Creates an IT from an AST
  -/
  def create (ast : AST) : InheritanceTree := Id.run do
    let mut it : InheritanceTree := InheritanceTree.emptyTree

    for sd in ast.sigDelcs do
      match sd.extension with
        | sigExt.extends e =>
          for name in sd.names do
            let parentName := (e.type.getReqVariables)[0]!
            let parentDecl :=
              (ast.sigDelcs.filter fun (sd) => sd.names.contains parentName).get! 0
            it := it.updateNodeExChild
              parentName parentDecl.abs name

        | sigExt.in i =>
          let parentNames := i.type.getReqVariables
          for parentName in parentNames do
            for name in sd.names do
              let parentDecl :=
                (ast.sigDelcs.filter fun (sd) => sd.names.contains parentName).get! 0
              it := it.updateNodeInChild parentName parentDecl.abs name
        | sigExt.none => continue

    return it

  /--
  Combines the given strings with & (Alloy operator for set intersection)
  -/
  private def product
    (e : String)
    (l : List (String))
    : List (TSyntax `term × List (String)) := Unhygienic.run do
      match l with
        | [] => do
          return []
        | h :: t => do
          let term ← `(
            $(mkIdent ``ThoR.SetMultPredicates.no)
              ((∻ $(mkIdent e.toName)) & (∻ $(mkIdent h.toName))))
          let termMembers : List (String) := [e, h]

          return [(term,  termMembers)] ++ (product e t)

  /--
  Combines the given List pairwise with & (Alloy operator for set intersection)
  -/
  private def pairwise_combination (input : List (String))
  : List (TSyntax `term × List (String)) :=
    match input with
      | [] => []
      | h :: t => (product h t) ++ (pairwise_combination t)

  /--
  Joins the given terms with and (∧) to create the conjunction of all subterms
  -/
  private def joinTermsWithAnd
    (input : List (TSyntax `term × List (String)))
    : (TSyntax `term ) := Unhygienic.run do
      if input.isEmpty then
        let result ← `($(mkIdent "".toName))
        return (result)

      else
        let firstInput := input.get! 0

        let mut result : TSyntax `term
            ← `($(firstInput.1))

        let mut resultMembers : List (String) := firstInput.2

        for term in (input.drop 1) do
          let newResult ← `($result ∧ $(term.1))
          result := newResult

          resultMembers := resultMembers.append term.2

        return result

  /--
  Create commands to create axioms representing the logical propositions that
  follow from the inheritance relationships for signatures in Alloy
  -/
  def createAxiomsCommand
    (it: InheritanceTree)
    (blockName : Name)
    : List (TSyntax `command) := Unhygienic.run do

    let mut commands : List (TSyntax `command) := []

    if it.nodes.isEmpty then -- no need to create if not needed.
      return commands
    else

      -- Name of the Namespace for the inheritance rule axioms
      let namespaceName := s!"{blockName}.inheritance_facts".toName

      --NamespaceBegin
      commands := commands.concat
        (← `(namespace $(mkIdent namespaceName)))

      --Relation Base
      let defsBaseType : TSyntax `command ←
        `(variable { $(baseType.getIdent) : Type }
          [ $(mkIdent ``ThoR.TupleSet) $(baseType.getIdent) ]
          [ $(mkIdent (s!"{blockName}.vars").toName) $(baseType.getIdent) ]
        )

      commands := commands.concat defsBaseType

      -- List of all pairs of the following form:
      -- - first item in pair: axiom body
      -- - second item in pair: list of all names of all signatures that appear in the axiom body
      let mut termsWithMembers
        : List (TSyntax `term × List (String)) := []

      let mut allMembers : List (String) := []

      for node in it.nodes do

        -- add namespace to parent
        let parentName := s!"{blockName}.vars.{node.name}"

        -- add namspaces to children
        let exChildren := node.exChildren.map
          fun (exChild) => s!"{blockName}.vars.{exChild}"
        let inChildren := node.inChildren.map
          fun (inChild) => s!"{blockName}.vars.{inChild}"

        let allChildren := (exChildren ++ inChildren)

        if !(allChildren.isEmpty) then

          -- Axioms for abstract
          if node.abs then

            let firstChild := allChildren.get! 0

            --Initialise HoldingLists
            let mut terms : TSyntax `term
              ← `((∻ $(mkIdent firstChild.toName)))

            let mut termMembers : List (String)
              := [firstChild]

            -- Fill Lists
            for child in (allChildren.drop 1) do
              terms ← `($terms + (∻ $(mkIdent child.toName)))
              termMembers := termMembers.concat child

            -- final AxiomBody
            let term ← `(((∻ $(mkIdent parentName.toName)) ≡ $terms))

            termMembers := termMembers.concat parentName

            termsWithMembers :=
              termsWithMembers.concat (term, termMembers)

            for member in termMembers do
              if !(allMembers.contains member) then
                allMembers := allMembers.concat member

          --exclusive extends combinations
          let mut pwec := pairwise_combination allChildren
          -- not to be included pairs
          let pwci := pairwise_combination inChildren
          pwec := pwec.filter fun (elem) => !(pwci.contains elem)
          if !(pwec.isEmpty) then
              termsWithMembers := termsWithMembers.append pwec

              for combination in pwec do
                for member in combination.2 do
                  if !(allMembers.contains member) then
                    allMembers := allMembers.concat member

          for child in allChildren do

            let term : TSyntax `term ←
            `(((∻ $(mkIdent child.toName)) ⊂
              (∻ $(mkIdent parentName.toName))))

            let termMembers : List (String) :=
              [child, parentName]

            termsWithMembers :=
              termsWithMembers.concat (term, termMembers)

            for member in termMembers do
              if !(allMembers.contains member) then
                allMembers := allMembers.concat member

      -- Create Axioms
      for member in allMembers do
        let termsWithMember :=
          termsWithMembers.filter fun (twm) => (twm.2.contains member)

        if !(termsWithMember.isEmpty) then

          let axiomName := s!"{member.toName.lastComponentAsString}".toName
          let joinedTerms := joinTermsWithAnd termsWithMember
          let command ← `(axiom $(mkIdent axiomName) : $(joinedTerms))

          commands := commands.concat command

      --NamespaceEnd
      commands := commands.concat
        (← `(end $(mkIdent namespaceName)))

      return commands

  end InheritanceTree

end Alloy