/- I need `Type _` (with the underscore) to allow those types to live in any
universe at any level. If I omit that and, for example, the field
`Semantics.model` is defined in some instance depending on another type,
like `Atom`, there would be universe inconsistencies. -/


import Mathlib.Data.Set.Defs

namespace Logic

structure ProofSystem (Form : Type _) where
  entails : Set Form → Form → Prop
notation:50 Γ " ⊢[" ps "] " φ => ProofSystem.entails ps Γ φ

namespace ProofSystem

def is_tauto {Form : Type _} (ps : ProofSystem Form) (φ : Form) : Prop :=
  ps.entails ∅ φ
notation:50 "⊢[" ps "] " φ => is_tauto ps φ

end ProofSystem


structure Semantics (Form : Type _) where
  model : Type _
  satisfies : model → Form → Prop

namespace Semantics

def is_sem_conseq {Form : Type _} (sem : Semantics Form)
    (Γ : Set Form) (φ : Form) : Prop :=
  ∀ (M : sem.model), (∀ ψ ∈ Γ, sem.satisfies M ψ) → sem.satisfies M φ
notation:50 Γ " ⊨[" sem "] " φ => is_sem_conseq sem Γ φ

def is_valid {Form : Type _} (sem : Semantics Form) (φ : Form) : Prop :=
  sem.is_sem_conseq ∅ φ
notation:50 "⊨[" sem "] " φ => is_valid sem φ

end Semantics


def is_sound_strong {Form : Type _} (ps : ProofSystem Form) (sem : Semantics Form) : Prop :=
  ∀ (Γ : Set Form) (φ : Form), (Γ ⊢[ps] φ) → (Γ ⊨[sem] φ)

def is_sound_weak {Form : Type _} (ps : ProofSystem Form) (sem : Semantics Form) : Prop :=
  ∀ (φ : Form), (⊢[ps] φ) → (⊨[sem] φ)

def is_complete_strong {Form : Type _} (ps : ProofSystem Form) (sem : Semantics Form) : Prop :=
  ∀ (Γ : Set Form) (φ : Form), (Γ ⊨[sem] φ) → (Γ ⊢[ps] φ)

def is_complete_weak {Form : Type _} (ps : ProofSystem Form) (sem : Semantics Form) : Prop :=
  ∀ (φ : Form), (⊨[sem] φ) → (⊢[ps] φ)

end Logic
