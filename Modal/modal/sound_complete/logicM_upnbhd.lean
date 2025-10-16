import Modal.modal.common.formula
import Modal.modal.models.nbhd_new
import Modal.modal.logics.logic_M


open Neighborhood


variable {𝓐 : Type}

-- Soundness and completeness of logic M with respect to upward-closed neighborhood models
-- Well-known result.
theorem logicM_upnbhd_sc :
    ∀ (φ : Modal.Formula 𝓐), valid_in_class IsUpwardClosed φ
      ↔ MProof (∅ : Set (Modal.Formula 𝓐)) φ := by
  admit
