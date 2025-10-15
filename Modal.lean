-- import Modal.Basic  -- it is empty at the moment

-- common utilities
import Modal.common.inference
import Modal.common.entailment
import Modal.common.consistency

-- classical propositional logic (CPL)
import Modal.cpl.syntax
import Modal.cpl.formula
import Modal.cpl.cpl

-- modal logic
import Modal.modal.common.syntax
import Modal.modal.common.formula
import Modal.modal.common.axioms_rules

-- modal logic systems
import Modal.modal.logics.logic_E
import Modal.modal.logics.logic_K
import Modal.modal.logics.logic_M

-- models
--import Modal.modal.models.kripke
--import Modal.modal.models.nbhd
--import Modal.modal.models.dual

-- soundness and completeness results
--import Modal.modal.sound_complete.logicK_kripke
--import Modal.modal.sound_complete.logicM_dual
--import Modal.modal.sound_complete.logicM_upnbhd
--import Modal.modal.sound_complete.logicE_nbhd
