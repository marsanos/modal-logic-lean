import Modal.cpl.cpl
import Modal.modal.common.formula
import Modal.modal.common.axioms_rules


open Modal

variable {𝓐 : Type}

inductive MProof : Set (Formula 𝓐) → Formula 𝓐 → Prop where
  | assumption {Γ : Set (Formula 𝓐)} {p : Formula 𝓐}
      (h : p ∈ Γ) :
      MProof Γ p
  | cpl {Γ : Set (Formula 𝓐)} {φ : Formula 𝓐}
      (h_cpl : (CPL.Entailment (Formula 𝓐)).entails ∅ ((to_cpl 𝓐) φ)) :
      MProof Γ φ
  | re {Γ : Set (Formula 𝓐)} {φ ψ : Formula 𝓐}
      (h_prem : MProof Γ (Rules.re φ ψ).premise) :
      MProof Γ (Rules.re φ ψ).conclusion
  | m {Γ : Set (Formula 𝓐)} {φ ψ : Formula 𝓐} :
      MProof Γ (Axioms.m φ ψ)

def MEntailment : EntailmentSystem :=
  { formula := Formula 𝓐
    entails := MProof }
