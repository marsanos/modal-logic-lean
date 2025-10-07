import Modal.cpl.proof
import Modal.modal.formula


open CPLSeq ModalFormula


-- α is the set of atomic propositions
structure KripkeFrame where
  world : Type
  rel : world → world → Prop

structure KripkeModel (α : Type) where
  frame : KripkeFrame
  val : frame.world → α → Prop



variable {α : Type}

-- Defines truth at a specific world w, that is m, w ⊨ φ.
def world_sat (m : KripkeModel α) (w : m.frame.world) : ModalFormula α → Prop
  | .atom a   => m.val w a
  | .bot      => False
  | .impl φ ψ => world_sat m w φ → world_sat m w ψ
  | .box φ    => ∀ v, m.frame.rel w v → world_sat m v φ
  | .dia φ    => ∃ v, m.frame.rel w v ∧ world_sat m v φ

-- Defines truth in an entire model m, that is m ⊨ φ.
def model_sat (m : KripkeModel α) (φ : ModalFormula α) : Prop :=
  ∀ w, world_sat m w φ

-- Defines truth in an entire model f, that is f ⊨ φ.
def frame_sat (f : KripkeFrame) (φ : ModalFormula α) : Prop :=
  ∀ val, model_sat ⟨f, val⟩ φ

-- Defines truth in all possible models, that is ⊨ φ.
def kripke_valid (φ : ModalFormula α) : Prop :=
  ∀ (f : KripkeFrame), frame_sat f φ

-- Notation
notation m ", " w " ⊨ " φ => world_sat m w φ
infix:45 " ⊨ " => model_sat
infix:45 " ⊨ " => frame_sat
prefix:45 "⊨ " => kripke_valid
