import Mathlib.Data.Set.Basic
import Modal.common.logic
import Modal.cpl.formula


namespace CPL

def proof_system (Atom : Type) : Logic.ProofSystem (Formula Atom) :=
  { entails := fun _ _ => by admit }


structure Valuation (Form : Type) [Syntax Form] where
  val : Form → Prop
  h_val_bot : val ⊥ = False
  h_val_impl : ∀ φ ψ, val (φ → ψ) = (val φ → val ψ)

def semantics (Atom : Type) : Logic.Semantics (Formula Atom) :=
  { model := Valuation (Formula Atom)
    satisfies := fun v φ => v.val φ }


theorem is_sound_strong (Atom : Type) :
    Logic.is_sound_strong (proof_system Atom) (semantics Atom) :=
  by admit

theorem is_complete_strong (Atom : Type) :
     Logic.is_complete_strong (proof_system Atom) (semantics Atom) :=
  by admit

/- TODO: I may need to define specific proof systems for CPL.
         I will do it whenever (if ever) I need it.
         Indeed, a proof system is already done in `_sequents.lean`. -/

end CPL
