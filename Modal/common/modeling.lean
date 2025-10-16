import Mathlib.Data.Set.Basic


class HasModels (𝓕 : Type) where
  models : Set 𝓕 → 𝓕 → Prop
notation Γ " ⊨ " φ:50 => HasModels.models Γ φ
