import Modal.cpl.proof
import Modal.modal.formula
import Modal.modal.axioms_rules


open ModalAxioms ModalRules CPLSeq ModalFormula

variable {α : Type} [ModalSyntax α]

inductive MProof : ModalFormula α → Prop where
  | cpl {p : ModalFormula α} (h_cpl : CPLProof p) : MProof p
  | rl_re {p q : ModalFormula α} (h_prem : MProof (rl_re p q).premise) :
                                           MProof (rl_re p q).conclusion
  | ax_dia {p : ModalFormula α} : MProof (ax_dia p)
  | ax_m {p q : ModalFormula α} : MProof (ax_m p q)
