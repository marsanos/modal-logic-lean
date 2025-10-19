/- I use `Type _` to allow those types to live in any
universe at any level. If I omit that and, for example,
the field `Semantics.model` is defined in some instance
depending on another type, like `Atom`, there would be
universe inconsistencies. -/


import Mathlib.Data.Set.Defs


namespace Logic

class ProofSystem where
  form : Type _  -- formulas
  entails : Set form → form → Prop
notation:50 Γ " ⊢[" P "] " φ => (fun Γ P φ => P.entails Γ φ)

def is_tauto (P : ProofSystem) (φ : P.form) : Prop :=
  P.entails ∅ φ
notation:50 "⊢[" P "] " φ => (fun P φ => P.is_tauto φ)


class Semantics where
  form : Type _  -- formulas
  model : Type _  -- models
  satisfies : model → form → Prop

def is_sem_conseq (S : Semantics) (Γ : Set S.form) (φ : S.form) : Prop :=
  ∀ (M : S.model), (∀ ψ ∈ Γ, S.satisfies M ψ) → S.satisfies M φ
notation:50 Γ " ⊨[" S "] " φ:50 => is_sem_conseq S Γ φ

def is_valid (S : Semantics) (φ : S.form) : Prop :=
  is_sem_conseq S ∅ φ
notation:50 "⊨[" S "] " φ => (fun S φ => S.is_valid φ)


-- We need to tell Lean how to convert ps.form into sem.form,
-- that's why Γ' and φ'.
def is_sound (ps : ProofSystem) (sem : Semantics)
             (h_eq_form : ps.form = sem.form) : Prop :=
  ∀ (Γ : Set ps.form) (φ : ps.form),
    let Γ' := Set.image (Eq.mp h_eq_form) Γ
    let φ' := Eq.mp h_eq_form φ
    ps.entails Γ φ → is_sem_conseq sem Γ' φ'

def is_complete (ps : ProofSystem) (sem : Semantics)
                (h_eq_form : ps.form = sem.form) : Prop :=
  ∀ (Γ : Set ps.form) (φ : ps.form),
    let Γ' := Set.image (Eq.mp h_eq_form) Γ
    let φ' := Eq.mp h_eq_form φ
    is_sem_conseq sem Γ' φ' → ps.entails Γ φ

end Logic
