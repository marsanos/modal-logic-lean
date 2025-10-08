import Modal.modal.formula
import Modal.modal.models.nbhd
import Modal.modal.logics.logic_M


open ModalFormula Neighborhood


variable {α : Type}

-- well-known result
theorem logicM_upnbhd_sc :
    ∀ (φ : ModalFormula α), valid_in_class IsUpwardClosed φ ↔ MProof φ := by
    sorry
