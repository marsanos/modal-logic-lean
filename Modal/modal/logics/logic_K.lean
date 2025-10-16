import Modal.cpl.entailment
import Modal.modal.common.formula
import Modal.modal.common.axioms_rules


open Modal

variable {𝓐 : Type}

inductive KProof : Set (Formula 𝓐) → Formula 𝓐 → Prop where
  | assumption {Γ : Set (Formula 𝓐)} {p : Formula 𝓐}
      (h : p ∈ Γ) :
      KProof Γ p
  | cpl {Γ : Set (Formula 𝓐)} {φ : Formula 𝓐}
      (h_cpl : (CPL.entails ∅ ((to_cpl 𝓐) φ))) :
      KProof Γ φ
  | re {Γ : Set (Formula 𝓐)} {φ ψ : Formula 𝓐}
      (h_prem : KProof Γ (Rules.re φ ψ).premise) :
      KProof Γ (Rules.re φ ψ).conclusion
  | nec {Γ : Set (Formula 𝓐)} {φ : Formula 𝓐}
      (h_prem : KProof Γ (Rules.nec φ).premise) :
      KProof Γ (Rules.nec φ).conclusion
  | k {Γ : Set (Formula 𝓐)} {φ ψ : Formula 𝓐} :
      KProof Γ (Axioms.k φ ψ)
