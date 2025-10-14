/- I do not care how the proof system is defined,
as long as it satisfies the needed metatheorems. -/


import Modal.cpl.syntax
import Mathlib.Data.Set.Defs

namespace CPL

def has_proof {𝓕 : Type} [Syntax 𝓕] (Γ : Set 𝓕) (φ : 𝓕) : Prop := by
  admit

notation:50 Γ " ⊢ " φ => has_proof Γ φ
notation:50 "⊢ " φ => has_proof ∅ φ

variable {𝓕 : Type} [Syntax 𝓕]

-- A valuation is a function from formulas to propositions that respects
-- the classical propositional connectives.
-- So we need to say what the valuation function is, and prove
-- that it respects ⊥ and → (the basic connectives).
-- A valuation is the concept of model in CPL.
structure Valuation (𝓕 : Type) [Syntax 𝓕] where
  eval : 𝓕 → Prop
  eval_bot : eval ⊥ = False
  eval_impl : ∀ φ ψ, eval (φ → ψ) = (eval φ → eval ψ)

def models_set (v : Valuation 𝓕) (Γ : Set 𝓕) : Prop :=
  ∀ ψ, ψ ∈ Γ → v.eval ψ

def semantic_consequence (Γ : Set 𝓕) (φ : 𝓕) : Prop :=
  ∀ (v : Valuation 𝓕), models_set v Γ → v.eval φ

notation:50 Γ " ⊨ " φ => semantic_consequence Γ φ

-- that is, is a tautology
def is_valid (φ : 𝓕) : Prop :=
  ∀ (v : Valuation 𝓕), v.eval φ

-- provable formulas are tautologies
-- The proof of this would depend on how the CPL proof system is defined.
theorem cpl_sound_weak : ∀ {φ : 𝓕}, (∅ ⊢ φ) → (∅ ⊨ φ) := by
  admit

theorem cpl_sound_strong : ∀ {Γ : Set 𝓕} {φ : 𝓕}, (Γ ⊢ φ) → (Γ ⊨ φ) := by
  admit

end CPL
