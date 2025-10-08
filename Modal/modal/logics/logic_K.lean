import Modal.cpl.proof
import Modal.modal.formula
import Modal.modal.axioms_rules


open ModalAxioms ModalRules CPLSeq ModalFormula

variable {α : Type} [ModalSyntax α]

inductive KProof : ModalFormula α → Prop where
  | classical {p : ModalFormula α} (h : CPLProof p) : KProof p
  | rl_re {p q : ModalFormula α} (h : KProof (rl_re p q).premise) :
                                      KProof (rl_re p q).conclusion
  | ax_dia {p : ModalFormula α} : KProof (ax_dia p)
  | rl_nec {p : ModalFormula α} (h : KProof (rl_nec p).premise) :
                                     KProof (rl_nec p).conclusion
  | ax_k {p q : ModalFormula α} : KProof (ax_k p q)
