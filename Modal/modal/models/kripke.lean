import Modal.modal.common.formula


namespace Kripke

open CPL


structure Frame where
  world : Type
  rel : world → world → Prop

-- 𝓐 is the set of atomic propositions
structure Model (𝓐 : Type) where
  frame : Frame
  val : frame.world → 𝓐 → Prop


variable {𝓐 : Type}

-- Defines truth at a specific world w, that is m, w ⊨ φ.
def world_sat (m : Model 𝓐) (w : m.frame.world) : Modal.Formula 𝓐 → Prop
  | .atom a   => m.val w a
  | .bot      => False
  | .impl φ ψ => world_sat m w φ → world_sat m w ψ
  | .box φ    => ∀ v, m.frame.rel w v → world_sat m v φ

-- Defines truth in an entire model m, that is m ⊨ φ.
def model_sat (m : Model 𝓐) (φ : Modal.Formula 𝓐) : Prop :=
  ∀ w, world_sat m w φ

-- Defines truth in an entire model f, that is f ⊨ φ.
def frame_sat (f : Frame) (φ : Modal.Formula 𝓐) : Prop :=
  ∀ val, model_sat ⟨f, val⟩ φ

-- Defines truth in all possible models, that is ⊨ φ.
def valid (φ : Modal.Formula 𝓐) : Prop :=
  ∀ (f : Frame), frame_sat f φ

-- Defines truth in all frames satisfying a given class/property.
def valid_in_class (P : Frame → Prop) (φ : Modal.Formula 𝓐) : Prop :=
  ∀ (f : Frame), P f → frame_sat f φ

end Kripke
