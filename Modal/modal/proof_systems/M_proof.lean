import Modal.cpl.proof
import Modal.modal.common.formula
import Modal.modal.common.axioms_rules


namespace Modal.ProofSystems.M

inductive proof {Atom : Type} : Set (Formula Atom) → Formula Atom → Prop where
  | assumption {Γ : Set (Formula Atom)} {p : Formula Atom}
      (h : p ∈ Γ) :
      proof Γ p
  | cpl {Γ : Set (Formula Atom)} {φ : Formula Atom}
      (h_cpl : (CPL.proof_system (Formula Atom)).entails ∅ (to_cpl φ)) :
      proof Γ φ
  | re {Γ : Set (Formula Atom)} {φ ψ : Formula Atom}
      (h_prem : proof Γ (Rules.re φ ψ).premise) :
      proof Γ (Rules.re φ ψ).conclusion
  | m {Γ : Set (Formula Atom)} {φ ψ : Formula Atom} :
      proof Γ (Axioms.m φ ψ)

instance proof_system (Atom : Type) : Logic.ProofSystem :=
  { form := Formula Atom,
    entails := proof }

end Modal.ProofSystems.M
