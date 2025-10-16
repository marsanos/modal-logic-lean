import Modal.modal.common.formula
import Modal.modal.models.nbhd_new
import Modal.modal.logics.logic_E


variable {𝓐 : Type}

-- Soundness and completeness of logic E with respect to neighborhood models
-- Well-known result
theorem logicE_nbhd_sc :
    ∀ (φ : Modal.Formula 𝓐), Neighborhood.valid φ ↔ EProof (∅ : Set (Modal.Formula 𝓐)) φ := by
  admit
