-- import Modal.Basic  -- empty at the moment

-- common utilities
import Modal.common.consistency
import Modal.common.entailment
import Modal.common.inference
import Modal.common.modeling
import Modal.common.syntax

-- classical propositional logic
import Modal.cpl.entailment
import Modal.cpl.formula
import Modal.cpl.modeling
import Modal.cpl.sound_complete
import Modal.cpl.syntax

-- modal logic
import Modal.modal.common.axioms_rules
import Modal.modal.common.formula
import Modal.modal.common.syntax

-- modal logic systems
import Modal.modal.logics.logic_E
import Modal.modal.logics.logic_K
import Modal.modal.logics.logic_M

-- models
import Modal.modal.models.dual
import Modal.modal.models.kripke_new
import Modal.modal.models.nbhd_new

-- soundness and completeness results
import Modal.modal.sound_complete.logicE_nbhd
import Modal.modal.sound_complete.logicK_kripke
--import Modal.modal.sound_complete.logicM_dual
import Modal.modal.sound_complete.logicM_upnbhd
