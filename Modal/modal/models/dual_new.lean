import Modal.modal.common.formula
import Modal.cpl.syntax
import Modal.common.syntax


namespace Dual

open CPL.Syntax Common.Syntax Modal.Syntax

structure Frame where
  n_world : Type
  p_world : Type
  rel : (n_world ⊕ p_world) → (n_world ⊕ p_world) → Prop

abbrev Frame.world (F : Frame) := F.n_world ⊕ F.p_world

structure Model (𝓕 : Type) [HasBot 𝓕] [HasImpl 𝓕] [HasBox 𝓕] where
  frame : Frame
  sat : frame.world → 𝓕 → Prop
  h_bot : ∀ w, ¬(sat w HasBot.bot)
  h_impl : ∀ w φ ψ, (sat w (HasImpl.impl φ ψ)) ↔ (sat w φ → sat w ψ)
  h_box : ∀ w φ, (sat w (HasBox.box φ)) ↔
    match w with
    | .inl wn => ∀ v, frame.rel (.inl wn) v → sat v φ
    | .inr wp => ∃ v, frame.rel (.inr wp) v ∧ sat v φ


-- Defines truth at a specific world w, that is m, w ⊨ φ.
variable {𝓕 : Type} [HasBot 𝓕] [HasImpl 𝓕] [HasBox 𝓕]

-- Defines truth at a specific world w, that is m, w ⊨ φ.
def world_sat (m : Model 𝓕) (w : m.frame.world) : 𝓕 → Prop :=
  fun φ => m.sat w φ

-- Defines truth in an entire model m, that is m ⊨ φ.
def model_sat (m : Model 𝓕) (φ : 𝓕) : Prop :=
  ∀ w, world_sat m w φ

-- Defines truth in an entire model f, that is f ⊨ φ.
def frame_sat (f : Frame) (φ : 𝓕) : Prop :=
  ∀ (sat : f.world → 𝓕 → Prop)
    (h_bot : ∀ w, ¬(sat w HasBot.bot))
    (h_impl : ∀ w φ ψ, (sat w (HasImpl.impl φ ψ)) ↔ (sat w φ → sat w ψ))
    (h_box : ∀ w φ, (sat w (HasBox.box φ)) ↔
      match w with
      | .inl wn => ∀ v, f.rel (.inl wn) v → sat v φ
      | .inr wp => ∃ v, f.rel (.inr wp) v ∧ sat v φ),
    model_sat ⟨f, sat, h_bot, h_impl, h_box⟩ φ

-- Defines truth in all possible models, that is ⊨ φ.
def valid (φ : 𝓕) : Prop :=
  ∀ (f : Frame), frame_sat f φ

-- Defines truth in all frames satisfying a given class/property.
def valid_in_class (P : Frame → Prop) (φ : 𝓕) : Prop :=
  ∀ (f : Frame), P f → frame_sat f φ





/-
-- some derived results that may be useful later

theorem world_sat_neg {m : Model 𝓕} {w : m.frame.world} {φ : 𝓕} :
    world_sat m w (neg φ) ↔ ¬(world_sat m w φ) := by
  unfold neg world_sat
  change m.sat w (HasImpl.impl φ HasBot.bot) ↔ ¬m.sat w φ
  rw [m.h_impl]
  simp [m.h_bot]

theorem world_sat_or {m : Model 𝓕} {w : m.frame.world} {φ ψ : 𝓕} :
    world_sat m w (φ ∨ ψ) ↔ (world_sat m w φ ∨ world_sat m w ψ) := by
  unfold CPL.Syntax.or CPL.Syntax.neg world_sat
  change m.sat w (HasImpl.impl (HasImpl.impl φ HasBot.bot) ψ) ↔ (m.sat w φ ∨ m.sat w ψ)
  rw [m.h_impl, m.h_impl]
  simp [m.h_bot]
  by_cases h : m.sat w φ
  · simp [h]
  · simp [h]

theorem world_sat_and {m : Model 𝓕} {w : m.frame.world} {φ ψ : 𝓕} :
    world_sat m w (φ ∧ ψ) ↔ (world_sat m w φ ∧ world_sat m w ψ) := by
    sorry
/-
  unfold CPL.Syntax.and CPL.Syntax.neg world_sat
  change m.sat w (HasImpl.impl (HasImpl.impl φ (HasImpl.impl ψ HasBot.bot)) HasBot.bot) ↔ (m.sat w φ ∧ m.sat w ψ)
    rw [m.h_impl]
    change (m.sat w (HasImpl.impl φ (HasImpl.impl ψ HasBot.bot)) → m.sat w HasBot.bot) ↔ (m.sat w φ ∧ m.sat w ψ)
      let hbot : ∀ P : Prop, (P → m.sat w HasBot.bot) ↔ ¬P :=
        λ P => ⟨λ hP, by_contra (λ h, m.h_bot w (hP h)), λ hP h, (hP h).elim⟩
    rw [hbot]
  rw [m.h_impl]
  change (m.sat w φ → m.sat w (HasImpl.impl ψ HasBot.bot)) ↔ (m.sat w φ ∧ m.sat w ψ)
  have hbot2 : ∀ P : Prop, (P → m.sat w HasBot.bot) ↔ ¬P := by
    intro P; constructor
    · intro hP; by_contra h; exact m.h_bot w (hP h)
    · intro hP h; exfalso; exact hP h
  rw [hbot2]
  tauto
  tauto
-/

theorem world_sat_iff {m : Model 𝓕} {w : m.frame.world} {φ ψ : 𝓕} :
    world_sat m w (φ ↔ ψ) ↔ (world_sat m w φ ↔ world_sat m w ψ) := by
  sorry
/-
  unfold CPL.Syntax.iff
  -- φ ↔ ψ = (φ → ψ) ∧ (ψ → φ)
  rw [world_sat_and]
  -- Now we have: world_sat m w (φ → ψ) ∧ world_sat m w (ψ → φ)
  --              ↔ (world_sat m w φ ↔ world_sat m w ψ)
  simp only [world_sat, m.h_impl]
  constructor
  · intro ⟨h_forward, h_backward⟩
    -- h_forward : world_sat m w φ → world_sat m w ψ
    -- h_backward : world_sat m w ψ → world_sat m w φ
    constructor
    · exact h_forward
    · exact h_backward
  · intro h_iff
    constructor
    · exact h_iff.mp
    · exact h_iff.mpr
-/
-/

end Dual
