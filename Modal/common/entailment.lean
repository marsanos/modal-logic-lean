/- We have two notations defined for bot and neg,
one here and another in cpl/syntax.lean.
I hope this causes no problems.

It may seem odd that these properties (HasEntails, etc.)
are considered properties of the type of formulas. But I cannot
find a better way. They may be considered properties of
a logic but, then, what is a logic? -/


import Mathlib.Data.Set.Basic


class HasEntails (𝓕 : Type) where
  entails : Set 𝓕 → 𝓕 → Prop
notation Γ " ⊢ " φ:50 => HasEntails.entails Γ φ

--def is_tauto {𝓕 : Type} (φ : 𝓕) [HasEntails 𝓕] : Prop :=
--  ∅ ⊢ φ
