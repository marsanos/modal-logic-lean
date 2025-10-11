import Modal.modal.formula
import Modal.modal.models.nbhd
import Modal.modal.logics.logic_E


open ModalFormula


variable {α : Type}

-- Soundness and completeness of logic E with respect to neighborhood models
-- Well-known result
theorem logicE_nbhd_sc :
    ∀ (φ : ModalFormula α), Neighborhood.valid φ ↔ EProof φ := by
    admit
