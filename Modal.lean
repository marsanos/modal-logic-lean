-- common utilities
import Modal.common.inference_rule
import Modal.common.logic

-- classical propositional logic
import Modal.cpl.formula
import Modal.cpl.proof
import Modal.cpl.syntax

-- modal logic
import Modal.modal.common.axioms_rules
import Modal.modal.common.formula
import Modal.modal.common.syntax

-- modal logics (proof systems)
import Modal.modal.proof_systems.K_proof
import Modal.modal.proof_systems.E_proof
import Modal.modal.proof_systems.M_proof

-- models
import Modal.modal.models.dual
import Modal.modal.models.kripke
import Modal.modal.models.nbhd

-- soundness and completeness results
import Modal.modal.sound_complete.E_nbhd
import Modal.modal.sound_complete.K_kripke
--import Modal.modal.sound_complete.M_dual
import Modal.modal.sound_complete.M_upnbhd
