import Modal.modal.formula
import Modal.modal.models.dual
import Modal.modal.logics.logic_M


open ModalFormula Dual


variable {α : Type}

theorem logicM_dual_sound :
    ∀ (φ : ModalFormula α), MProof φ → valid φ := by
    sorry

theorem logicM_dual_complete :
    ∀ (φ : ModalFormula α), valid φ → MProof φ := by
    sorry

theorem logicM_dual_sc :
    ∀ (φ : ModalFormula α), valid φ ↔ MProof φ := by
    intro φ
    constructor
    · exact logicM_dual_complete φ
    · exact logicM_dual_sound φ
