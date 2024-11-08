/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
List example from Alloy Analyzer
examples -> systems -> lists.als
-/
#alloy lists

sig Element {}

abstract sig List {}

one sig EmptyList extends List {}

sig NonEmptyList extends List {
  element: Element,
  rest: List
}

fact ListGenerator {
  all list: List| all e: Element |
    some list': List | list'.rest = list and list'.element = e
}

assert FalseAssertion {
  all list: List | list != list
  }

end

#check lists.vars.element
#check lists.vars.Element
#check lists.vars.EmptyList
#check lists.vars.List
#check lists.vars.NonEmptyList
#check lists.vars.rest

#check lists.facts.ListGenerator

#check lists.asserts.FalseAssertion

#check lists.inheritance_facts.EmptyList
#check lists.inheritance_facts.List
#check lists.inheritance_facts.NonEmptyList

#print lists.asserts.FalseAssertion
