import Modal.cpl.proof
import Modal.cpl.syntax


namespace CPLMetatheorems

open CPLSeq CPLSyntax


variable {Form : Type} [CPLSyntax Form]

-- A valuation is a function from formulas to propositions that respects
-- the classical propositional connectives
structure Valuation (Form : Type) [CPLSyntax Form] where
  eval : Form → Prop
  eval_bot : eval ⊥ = False
  eval_impl : ∀ φ ψ, eval (φ → ψ) = (eval φ → eval ψ)

-- Notation for satisfaction under a valuation
notation:50 v " ⊨ " φ => Valuation.eval v φ

-- A formula is a tautology if it's true under all valuations
def is_tautology (φ : Form) : Prop :=
  ∀ (v : Valuation Form), v ⊨ φ

-- Sequent validity: Γ ⊢ A is valid if whenever all formulas in Γ are satisfied,
-- then A is also satisfied
def sequent_valid (Γ : Multiset Form) (A : Form) : Prop :=
  ∀ (v : Valuation Form), (∀ B ∈ Γ, v ⊨ B) → v ⊨ A

-- CPL Soundness for sequents: provable sequents are valid
theorem sequent_sound :
    ∀ {Γ : Multiset Form} {A : Form},
    CPLSeqProof (Γ ⊢ A) → sequent_valid Γ A := by
  sorry

-- CPL Soundness: provable formulas are tautologies
theorem cpl_sound :
    ∀ {φ : Form}, CPLProof φ → is_tautology φ := by
  intro φ h v
  unfold CPLProof at h
  have sound := sequent_sound h
  unfold sequent_valid at sound
  exact sound v (fun B hB => by cases Multiset.notMem_zero B hB)


end CPLMetatheorems
