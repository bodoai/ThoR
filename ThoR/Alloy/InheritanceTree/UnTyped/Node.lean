/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
namespace Alloy

  /--
  Represents a single extension node of the 'inheritance tree'
  An extension node can be an extends- or an in-extension node.
  -/
  structure Node where
    mk :: (name : String)
          (abs : Bool)
          (exChildren : List (String)) -- children of 'extends' extension
          (inChildren : List (String)) -- children of 'in' extension
  deriving Repr

  namespace Node

    /--
    creates a childless node
    -/
    def childlessNode (name: String) (abs : Bool) : Node :=
      { name := name,
        abs := abs,
        inChildren := [],
        exChildren := []}

    /--
    creates a node with a single inChild
    -/
    def oneInChildNode (name: String) (abs : Bool) (child: String) : Node :=
      { name := name,
        abs := abs,
        inChildren := [child],
        exChildren := []}

    /--
    creates a node with a single exChild
    -/
    def oneExChildNode (name: String) (abs : Bool) (child: String) : Node :=
      { name := name,
        abs := abs,
        inChildren := [],
        exChildren := [child]}

    /--
    adds a single inChild
    -/
    def addInChild (n: Node) (c : String) :=
      {n with inChildren := n.inChildren.append [c]}

    /--
    adds a single exChild
    -/
    def addExChild (n: Node) (c : String) :=
      {n with exChildren := n.exChildren.append [c]}

    instance : BEq Node where
      beq : Node -> Node -> Bool
        | n1,n2 => (n1.name == n2.name)

  end Node

end Alloy
