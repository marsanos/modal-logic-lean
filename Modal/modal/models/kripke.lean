import Modal.modal.common.formula


namespace Modal.Models.Kripke

structure Frame where
  world : Type
  rel : world → world → Prop

structure Model (Atom : Type) (h_frame : Frame → Prop) where
  frame : Frame
  h_frame : h_frame frame
  val : frame.world → Atom → Prop


-- Defines truth at a specific world w, that is m, w ⊨ φ.
def world_sat {Atom : Type} {h_frame : Frame → Prop}
    (m : Model Atom h_frame) (w : m.frame.world) : Modal.Formula Atom → Prop
  | .atom a   => m.val w a
  | .bot      => False
  | .impl φ ψ => world_sat m w φ → world_sat m w ψ
  | .box φ    => ∀ v, m.frame.rel w v → world_sat m v φ

-- Defines truth in an entire model m, that is m ⊨ φ.
def model_sat {Atom : Type} {h_frame : Frame → Prop}
    (m : Model Atom h_frame) (φ : Modal.Formula Atom) : Prop :=
  ∀ w, world_sat m w φ

instance semantics {Atom : Type} {h_frame : Frame → Prop} : Logic.Semantics :=
  { form := Formula Atom,
    model := Model Atom h_frame,
    satisfies := model_sat }

end Modal.Models.Kripke


-- Defines truth in an entire model f, that is f ⊨ φ.
--def frame_sat (f : Frame) (φ : Modal.Formula Atom) : Prop :=
--  ∀ val, model_sat ⟨f, val⟩ φ

-- Defines truth in all possible models, that is ⊨ φ.
--def valid (φ : Modal.Formula Atom) : Prop :=
--  ∀ (f : Frame), frame_sat f φ

-- Defines truth in all frames satisfying a given class/property.
--def valid_in_class (P : Frame → Prop) (φ : Modal.Formula Atom) : Prop :=
--  ∀ (f : Frame), P f → frame_sat f φ
