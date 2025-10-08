import Modal.modal.formula
import Modal.modal.models.kripke
import Modal.modal.logics.logic_K


open ModalFormula


variable {α : Type}

-- well-known result
theorem logicK_kripke_sc :
    ∀ (φ : ModalFormula α), Kripke.valid φ ↔ KProof φ := by
    sorry
