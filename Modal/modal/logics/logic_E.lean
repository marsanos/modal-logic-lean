import Modal.cpl.proof
import Modal.modal.formula
import Modal.modal.axioms_rules


open Modal.Axioms Modal.Rules

variable {α : Type}

inductive EProof : Modal.Formula α → Prop where
  | cpl {p : Modal.Formula α} (h_cpl : CPL.has_proof ∅ p) : EProof p
  | rl_re {p q : Modal.Formula α} (h_prem : EProof (rl_re p q).premise) :
                                            EProof (rl_re p q).conclusion
