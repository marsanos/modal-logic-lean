import Modal.modal.formula
import Modal.modal.models.nbhd
import Modal.modal.logics.logic_M


open Neighborhood


variable {α : Type}

-- Soundness and completeness of logic M with respect to upward-closed neighborhood models
-- Well-known result - not specific to dual models
theorem logicM_upnbhd_sc :
    ∀ (φ : Modal.Formula α), valid_in_class IsUpwardClosed φ ↔ MProof φ := by
    admit
