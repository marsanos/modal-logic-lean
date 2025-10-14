import Mathlib.Data.Multiset.Basic
import Modal.cpl.proof
import Modal.modal.formula
import Modal.modal.axioms_rules


open Modal.Axioms Modal.Rules

variable {α : Type}

inductive MProof : Modal.Formula α → Prop where
  | cpl {p : Modal.Formula α} (h_cpl : CPL.has_proof ∅ p) : MProof p
  | rl_re {p q : Modal.Formula α} (h_prem : MProof (rl_re p q).premise) :
                                            MProof (rl_re p q).conclusion
  | ax_m {p q : Modal.Formula α} : MProof (ax_m p q)

inductive MProof' (Γ : Multiset (Modal.Formula α)) : Modal.Formula α → Prop where
  | assumption {p : Modal.Formula α} (h : p ∈ Γ) : MProof' Γ p
  | cpl {p : Modal.Formula α} (h_cpl : CPL.has_proof ∅ p) : MProof' Γ p
  | rl_re {p q : Modal.Formula α} (h_prem : MProof' Γ (rl_re p q).premise) :
                                            MProof' Γ (rl_re p q).conclusion
  | ax_m {p q : Modal.Formula α} : MProof' Γ (ax_m p q)
