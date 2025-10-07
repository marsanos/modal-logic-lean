/-
This file contains code to transform a modal formula into a CPL one.
The goal is check if the result is a tautology in CPL.
The translation replaces each subformulas with a modal operator in its root
with a propositional variable. For example, `□p→p→□p` becomes `q→p→q`,
which is a tautology in CPL.
The function intended to be used from outside is `modalToCpl`.
-/

import Modal.cpl.syntax
import Modal.cpl.formula
import Modal.modal.syntax
import Modal.modal.formula

open ModalFormula CPLFormula

/-
State of the transformation. It contains:
- `nextVar`: the number of the next propositional variable available for use;
- `modalMap`: a list of pairs `(modal_formula, cpl_formula)` that maps
  each modal formula to its corresponding propositional variable. I insist
  that `cpl_formula` is always a propositional variable, not a more complex formula.
-/

structure ModalToCplState (α : Type) where
  nextVar : Nat
  modalMap : List (ModalFormula α × CPLFormula Nat)

-- to find if a modal subformula has already been assigned a variable
def findModalInMap {α : Type} [DecidableEq α]
    (f : ModalFormula α) (map : List (ModalFormula α × CPLFormula Nat)) :
    Option (CPLFormula Nat) :=
  map.find? (fun (mf, _) => decide (mf = f)) |> .map Prod.snd

-- to get a fresh propositional variable
def getFreshVar {α : Type} (state : ModalToCplState α) :
    (CPLFormula Nat × ModalToCplState α) :=
  let newVar := CPLFormula.atom state.nextVar
  (newVar, { state with nextVar := state.nextVar + 1 })

-- main transformation function
def modalToCpl {α : Type} [DecidableEq α]
    (f : ModalFormula α) : ModalToCplState α → (CPLFormula Nat × ModalToCplState α) :=
  fun state =>
    match f with
    | .atom _ =>
      match findModalInMap f state.modalMap with
      | some cplVar => (cplVar, state)
      | none =>
        let (freshVar, state1) := getFreshVar state
        let newState := { state1 with modalMap := (f, freshVar) :: state1.modalMap }
        (freshVar, newState)
    | .bot => (CPLFormula.bot, state)
    | .impl p q =>
      let (p', state1) := modalToCpl p state
      let (q', state2) := modalToCpl q state1
      (CPLFormula.impl p' q', state2)
    | .box _ =>
      match findModalInMap f state.modalMap with
      | some cplVar => (cplVar, state)
      | none =>
        let (freshVar, state1) := getFreshVar state
        let newState := { state1 with modalMap := (f, freshVar) :: state1.modalMap }
        (freshVar, newState)
    | .dia _ =>
      match findModalInMap f state.modalMap with
      | some cplVar => (cplVar, state)
      | none =>
        let (freshVar, state1) := getFreshVar state
        let newState := { state1 with modalMap := (f, freshVar) :: state1.modalMap }
        (freshVar, newState)

-- final function to transform a modal formula starting with empty state
def modalToCplSimple {α : Type} [DecidableEq α]
    (f : ModalFormula α) : CPLFormula Nat :=
  let initialState : ModalToCplState α := { nextVar := 0, modalMap := [] }
  let (result, _) := modalToCpl f initialState
  result




-- Example formulas to test
#eval modalToCplSimple (.atom 0)  -- 0 becomes 0
#eval modalToCplSimple (□ .atom 0)  -- □0 becomes 0
#eval modalToCplSimple ((□ .atom 0) → .atom 0) -- □0→0 becomes 0→1
#eval modalToCplSimple ((□ .atom 0) → .atom 0 → (□ .atom 0))
  -- □0→0→□0 becomes 0→1→0
