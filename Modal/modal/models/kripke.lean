import Modal.modal.common.formula


namespace Modal.Models.Kripke

structure Frame where
  world : Type
  rel : world → world → Prop

namespace FramePpty
-- Common frame properties (conditions on accessibility relations)
-- When we need a particular type of frame, we can write
-- def ReflexiveFrame := { f : Frame // f.reflexive }
-- or
-- def S4_frame (f : Frame) : Prop := f.reflexive ∧ f.transitive
-- etc.
def reflexive (f : Frame) : Prop :=
  ∀ w : f.world, f.rel w w
def symmetric (f : Frame) : Prop :=
  ∀ w v : f.world, f.rel w v → f.rel v w
def transitive (f : Frame) : Prop :=
  ∀ w v u : f.world, f.rel w v → f.rel v u → f.rel w u
def euclidean (f : Frame) : Prop :=
  ∀ w v u : f.world, f.rel w v → f.rel w u → f.rel v u
def serial (f : Frame) : Prop :=
  ∀ w : f.world, ∃ v : f.world, f.rel w v
end FramePpty

structure Model (Atom : Type) where
  frame : Frame
  val : frame.world → Atom → Prop


-- Defines truth at a specific world w, that is m, w ⊨ φ.
def world_sat {Atom : Type} (m : Model Atom) (w : m.frame.world) :
    Modal.Formula Atom → Prop
  | .atom a   => m.val w a
  | .bot      => False
  | .impl φ ψ => world_sat m w φ → world_sat m w ψ
  | .box φ    => ∀ v, m.frame.rel w v → world_sat m v φ

-- Defines truth in an entire model m, that is m ⊨ φ.
def model_sat {Atom : Type} (m : Model Atom) (φ : Modal.Formula Atom) : Prop :=
  ∀ w, world_sat m w φ

def semantics {Atom : Type} : Logic.Semantics (Formula Atom) :=
  { model := Model Atom,
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
