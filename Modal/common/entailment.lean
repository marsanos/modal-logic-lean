/- We have two notations defined for bot and neg,
one here and another in cpl/syntax.lean.
I hope this causes no problems.

It may seem odd that these properties (HasEntails, etc.)
are considered properties of the type of formulas. But I cannot
find a better way. They may be considered properties of
a logic but, then, what is a logic? -/


import Mathlib.Data.Set.Basic


class EntailmentSystem where
  formula : Type
  entails : Set formula → formula → Prop
notation Γ " ⊢ " φ:50 => EntailmentSystem.entails Γ φ

class HasBot (𝓕 : Type) where
  bot : 𝓕
notation "⊥" => HasBot.bot

class HasNeg (𝓕 : Type) where
  neg : 𝓕 → 𝓕
prefix:40 "¬" => HasNeg.neg

def is_tauto {𝓔 : EntailmentSystem} (φ : 𝓔.formula) : Prop :=
  ∅ ⊢ φ
