/- I do not care what the actual proof system is for CPL,
as long as it satisfied the needed metatheorems. -/


import Modal.cpl.syntax
import Mathlib.Data.Multiset.Defs

namespace CPLProof

def CPLProof {Form : Type} [CPLSyntax Form] (A : Form) : Prop :=
  sorry


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

-- provable formulas are tautologies
theorem cpl_sound : ∀ {φ : Form}, CPLProof φ → is_tautology φ := by
  admit

end CPLProof
