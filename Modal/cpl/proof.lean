import Mathlib.Data.Set.Basic
import Modal.common.logic
import Modal.cpl.formula


namespace CPL

def proof_system (Atom : Type) : Logic.ProofSystem :=
  { form := Formula Atom
    entails : Set (Formula Atom) → Formula Atom → Prop := by admit }

def semantics (Atom : Type) : Logic.Semantics :=
  { form := Formula Atom
    model := by admit
    satisfies := by admit }

theorem is_sound (Atom : Type) :
    Logic.is_sound (proof_system Atom) (semantics Atom) (by rfl) :=
  by admit

theorem is_complete (Atom : Type) :
     Logic.is_complete (proof_system Atom) (semantics Atom) (by rfl) :=
  by admit

/- TODO: I may need to define specific proof systems and semantics for CPL.
         I will do it whenever (if ever) I need it.
         Indeed, a proof system is already done in `_sequents.lean`.
         And the semantics is defined in `_metatheorems.lean`. -/

end CPL
