import Modal.modal.formula
import Modal.modal.kripke_model
import Modal.modal.logic_K


open ModalFormula


variable {α : Type}

theorem logic_K_sound_and_complete :
    ∀ (φ : ModalFormula α), ⊨ φ ↔ KProof φ := by
  sorry
