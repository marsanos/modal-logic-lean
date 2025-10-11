/- The type φ is supposed to be the type of modal formulas,
but this works for anything with the appropriate syntax. -/


import Modal.modal.syntax
import Modal.common.inference

namespace ModalRules

variable {φ : Type} [ModalSyntax φ]

def rl_nec (p : φ) : InferenceRule1 φ  := ⟨p, □p⟩
def rl_re (p q : φ) : InferenceRule1 φ := ⟨p ↔ q, □p ↔ □q⟩

end ModalRules


namespace ModalAxioms

variable {φ : Type} [ModalSyntax φ]

def ax_t (p : φ) : φ   := □p → p
def ax_b (p : φ) : φ   := p → □(◇p)
def ax_4 (p : φ) : φ   := □p → □(□p)
def ax_5 (p : φ) : φ   := ◇p → □(◇p)
def ax_m (p q : φ) : φ := □(p∧q) → □p
def ax_k (p q : φ) : φ := □(p → q) → (□p → □q)
def ax_n : φ           := □⊤

end ModalAxioms
