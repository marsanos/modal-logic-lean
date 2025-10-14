import Modal.cpl.proof
import Modal.modal.formula
import Modal.modal.axioms_rules


open Modal.Axioms Modal.Rules

variable {α : Type}

inductive KProof : Modal.Formula α → Prop where
  | classical {p : Modal.Formula α} (h : CPL.has_proof ∅ p) : KProof p
  | rl_re {p q : Modal.Formula α} (h : KProof (rl_re p q).premise) :
                                       KProof (rl_re p q).conclusion
  | rl_nec {p : Modal.Formula α} (h : KProof (rl_nec p).premise) :
                                      KProof (rl_nec p).conclusion
  | ax_k {p q : Modal.Formula α} : KProof (ax_k p q)
