import Modal.cpl.proof
import Modal.cpl.syntax


namespace CPLMetatheorems

open CPLSeq CPLSyntax


variable {Form : Type} [CPLSyntax Form]

-- A valuation is a function from formulas to propositions that respects
-- the classical propositional connectives.
-- So we need to say what the valuation function is, and prove
-- that it respects ⊥ and → (the basic connectives).
structure Valuation (Form : Type) [CPLSyntax Form] where
  eval : Form → Prop
  eval_bot : eval ⊥ = False
  eval_impl : ∀ φ ψ, eval (φ → ψ) = (eval φ → eval ψ)

notation:50 v " ⊨ " φ => Valuation.eval v φ

def is_tautology (φ : Form) : Prop :=
  ∀ (v : Valuation Form), v ⊨ φ

def sequent_valid (Γ : Multiset Form) (A : Form) : Prop :=
  ∀ (v : Valuation Form), (∀ B ∈ Γ, v ⊨ B) → v ⊨ A

-- provable sequents are valid - well-known result
theorem sequent_sound :
    ∀ {Γ : Multiset Form} {A : Form},
    CPLSeqProof (Γ ⊢ A) → sequent_valid Γ A := by
  admit

-- provable formulas are tautologies
theorem cpl_sound : ∀ {φ : Form}, CPLProof φ → is_tautology φ := by
  intro φ h v
  unfold CPLProof at h
  have sound := sequent_sound h
  unfold sequent_valid at sound
  exact sound v (fun B hB => by cases Multiset.notMem_zero B hB)

end CPLMetatheorems
