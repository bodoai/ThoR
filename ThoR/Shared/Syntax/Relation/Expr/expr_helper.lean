/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.SymbolTable.varDecl

open Alloy
open Lean

namespace Shared.expr

  /--
  Replaces all calls to the callables from the List `callables`
  with their respective replacement
  in the given expression `e`
  -/
  def replaceCalls
    (e: expr)
    (callables : List (varDecl))
    : expr := Id.run do

      match e with
        | expr.string s =>

          -- Get the names of the callable elements
          let callableNames := callables.map fun c => c.name

          /-
          if the called name is contained in the callable elements

          note that this should alway be the case, since if it is not contianed
          the symbol table should throw an error
          -/
          if callableNames.contains s then

            -- Get the index of the callable (the lists are same since since it was mapped)
            let callableIndex := callableNames.indexOf s

            -- Get the callable element
            let calledElement := callables.get! callableIndex

            -- Return the expression with the fitting replacement name
            return expr.string
              (if calledElement.isRelation then
                (calledElement.getRelationReplacementName)
              else
                (calledElement.getSignatureReplacementName))

          return e

        | expr.callFromOpen sn =>
          let ns := sn.representedNamespace.getId.lastComponentAsString
          let nsSplit := ns.splitOn "."

          /-
          This should never be empty
          -/
          if !nsSplit.isEmpty then

            /-
            the called name is the last element of this split
            e.g. m1.a -> a is the called name
            -/
            let calledName := nsSplit.getLast!

            /-
            a namespace means that there is more than just the called name
            this has to be the case, since singular names are matched on string
            -/
            let namespacePresent := nsSplit.length > 1

            if namespacePresent then

              -- the complete namespace
              let sigNamespace :=
                ((nsSplit.take (nsSplit.length - 1)).drop 1).foldl
                  (fun result current => s!"{result}_{current}")
                  (nsSplit.get! 0)

              -- the namespace with the last element removed (assumend to be a sig name)
              let relNamespace :=
                ((nsSplit.take (nsSplit.length - 2)).drop 1).foldl
                  (fun result current => s!"{result}_{current}")
                  (nsSplit.get! 0)

              let possibleCalls := callables.filter
                fun c =>
                  -- the name has to be the name called
                  c.name = calledName &&

                  (
                  -- if its a relation
                  ( c.isRelation &&
                  -- the signature name hast to be correct
                  ( c.relationOf == nsSplit.get! (nsSplit.length - 2) &&
                  -- and the namespace hast to be correct
                    (c.openedFrom == relNamespace) ||
                  -- or not given for this
                    (c.openedFrom == "this" && relNamespace == "")))

                  ||

                  -- if its a signature
                  ( !c.isRelation &&
                  -- the namespace hast to be correct
                  ( c.openedFrom == sigNamespace) ||
                  -- or not given for this
                  (c.openedFrom == "this" && relNamespace == ""))

                  )

              -- Only one call should be possible (since the symbold table already checked)
              if possibleCalls.length == 1 then
                let calledElement := possibleCalls.get! 0

                let identifer := mkIdent
                  (if calledElement.isRelation then
                    calledElement.getFullRelationName.toName
                  else
                    calledElement.getFullSignatureName.toName)

                return expr.callFromOpen (Alloy.separatedNamespace.mk identifer)

          return e

        | expr.binaryRelOperation op e1 e2 =>
          expr.binaryRelOperation
            op
            (e1.replaceCalls callables)
            (e2.replaceCalls callables)

        | expr.unaryRelOperation op e =>
          expr.unaryRelOperation
            op
            (e.replaceCalls callables)

        | expr.dotjoin dj e1 e2 =>
          expr.dotjoin
            dj
            (e1.replaceCalls callables)
            (e2.replaceCalls callables)

        | _ => e

end Shared.expr
