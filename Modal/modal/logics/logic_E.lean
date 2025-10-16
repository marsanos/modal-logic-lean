import Modal.cpl.entailment
import Modal.modal.common.formula
import Modal.modal.common.axioms_rules


open Modal

variable {𝓐 : Type}

inductive EProof : Set (Formula 𝓐) → Formula 𝓐 → Prop where
  | assumption {Γ : Set (Formula 𝓐)} {p : Formula 𝓐}
      (h : p ∈ Γ) :
      EProof Γ p
  | cpl {Γ : Set (Formula 𝓐)} {φ : Formula 𝓐}
      (h_cpl : (CPL.entails ∅ ((to_cpl 𝓐) φ))) :
      EProof Γ φ
  | re {Γ : Set (Formula 𝓐)} {φ ψ : Formula 𝓐}
      (h_prem : EProof Γ (Rules.re φ ψ).premise) :
      EProof Γ (Rules.re φ ψ).conclusion
