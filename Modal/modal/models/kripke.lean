import Modal.cpl.proof
import Modal.modal.formula


namespace Kripke

open CPL ModalFormula


structure Frame where
  world : Type
  rel : world → world → Prop

-- α is the set of atomic propositions
structure Model (α : Type) where
  frame : Frame
  val : frame.world → α → Prop



variable {α : Type}

-- Defines truth at a specific world w, that is m, w ⊨ φ.
def world_sat (m : Model α) (w : m.frame.world) : ModalFormula α → Prop
  | .atom a   => m.val w a
  | .bot      => False
  | .impl φ ψ => world_sat m w φ → world_sat m w ψ
  | .box φ    => ∀ v, m.frame.rel w v → world_sat m v φ

-- Defines truth in an entire model m, that is m ⊨ φ.
def model_sat (m : Model α) (φ : ModalFormula α) : Prop :=
  ∀ w, world_sat m w φ

-- Defines truth in an entire model f, that is f ⊨ φ.
def frame_sat (f : Frame) (φ : ModalFormula α) : Prop :=
  ∀ val, model_sat ⟨f, val⟩ φ

-- Defines truth in all possible models, that is ⊨ φ.
def valid (φ : ModalFormula α) : Prop :=
  ∀ (f : Frame), frame_sat f φ

-- Defines truth in all frames satisfying a given class/property.
def valid_in_class (P : Frame → Prop) (φ : ModalFormula α) : Prop :=
  ∀ (f : Frame), P f → frame_sat f φ

end Kripke
