import Modal.modal.common.formula
import Modal.modal.models.kripke_new
import Modal.modal.logics.logic_K


variable {𝓐 : Type}

-- Soundness and completeness of logic K with respect to Kripke models
-- Well-known result.
theorem logicK_kripke_sc :
    ∀ (φ : Modal.Formula 𝓐), Kripke.valid φ ↔ KProof (∅ : Set (Modal.Formula 𝓐)) φ := by
  admit
