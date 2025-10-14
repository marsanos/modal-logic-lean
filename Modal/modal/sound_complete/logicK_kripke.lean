import Modal.modal.formula
import Modal.modal.models.kripke
import Modal.modal.logics.logic_K


variable {α : Type}

-- Soundness and completeness of logic K with respect to Kripke models
-- Well-known result
theorem logicK_kripke_sc :
    ∀ (φ : Modal.Formula α), Kripke.valid φ ↔ KProof φ := by
    admit
