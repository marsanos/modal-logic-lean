import Modal.cpl.proof
import Modal.modal.formula
import Modal.modal.axioms_rules


open ModalAxioms ModalRules CPL ModalFormula

variable {α : Type} [ModalSyntax α]

inductive EProof : ModalFormula α → Prop where
  | cpl {p : ModalFormula α} (h_cpl : CPLProof p) : EProof p
  | rl_re {p q : ModalFormula α} (h_prem : EProof (rl_re p q).premise) :
                                           EProof (rl_re p q).conclusion
