import Modal.cpl.proof
import Modal.modal.formula
import Modal.modal.axioms_rules


open ModalAxioms ModalRules CPLSeq ModalFormula

variable {α : Type} [ModalSyntax α]

inductive EProof : ModalFormula α → Prop where
  | classical {p : ModalFormula α} (h_cpl : CPLProof p) : EProof p
  | rl_re {p q : ModalFormula α} (h_prem : EProof (rl_re p q).premise) :
                                           EProof (rl_re p q).conclusion
  | ax_def_dia {p : ModalFormula α} : EProof (ax_def_dia p)
