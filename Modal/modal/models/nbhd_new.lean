import Modal.modal.common.formula
import Modal.cpl.syntax
import Modal.common.syntax


namespace Neighborhood

open CPL.Syntax Common.Syntax


structure Frame where
  world : Type
  nbhd : world → Set (Set world)

structure Model (𝓕 : Type) [HasBot 𝓕] [HasImpl 𝓕] [HasBox 𝓕] where
  frame : Frame
  sat : frame.world → 𝓕 → Prop
  h_bot : ∀ w, ¬(sat w HasBot.bot)
  h_impl : ∀ w φ ψ, (sat w (HasImpl.impl φ ψ)) ↔ (sat w φ → sat w ψ)
  h_box : ∀ w φ, {v | sat v φ} ∈ frame.nbhd w

class IsUpwardClosed (f : Frame) : Prop where
  is_up_closed : ∀ w (X Y : Set f.world), X ∈ f.nbhd w → X ⊆ Y → Y ∈ f.nbhd w


variable {𝓕 : Type} [HasBot 𝓕] [HasImpl 𝓕] [HasBox 𝓕]

-- Defines truth at a specific world w, that is m, w ⊨ φ.
def world_sat (m : Model 𝓕) (w : m.frame.world) : 𝓕 → Prop :=
  fun φ => m.sat w φ

-- Defines truth in an entire model m, that is m ⊨ φ.
def model_sat (m : Model 𝓕) (φ : 𝓕) : Prop :=
  ∀ w, world_sat m w φ

-- Defines truth in an entire frame f, that is f ⊨ φ.
def frame_sat (f : Frame) (φ : 𝓕) : Prop :=
  ∀ (sat : f.world → 𝓕 → Prop)
    (h_bot : ∀ w, ¬(sat w HasBot.bot))
    (h_impl : ∀ w φ ψ, (sat w (HasImpl.impl φ ψ)) ↔ (sat w φ → sat w ψ))
    (h_box : ∀ w φ, {v | sat v φ} ∈ f.nbhd w),
    model_sat ⟨f, sat, h_bot, h_impl, h_box⟩ φ

-- Defines truth in all possible models, that is ⊨ φ.
def valid (φ : 𝓕) : Prop :=
  ∀ (f : Frame), frame_sat f φ

-- Defines truth in all frames satisfying a given class/property.
def valid_in_class (P : Frame → Prop) (φ : 𝓕) : Prop :=
  ∀ (f : Frame), P f → frame_sat f φ

end Neighborhood
