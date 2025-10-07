/- The type φ is supposed to be the type of modal formulas,
but this works for anything with the appropriate syntax. -/


import Modal.modal.syntax
import Modal.common.inference

namespace ModalRules

variable {φ : Type} [ModalSyntax φ]

def rl_nec (p : φ) : InferenceRule1 φ := ⟨p, □p⟩
def rl_re (p q : φ) : InferenceRule1 φ := ⟨p ↔ q, □p ↔ □q⟩

end ModalRules


namespace ModalAxioms

variable {φ : Type} [ModalSyntax φ]

def ax_dia (p : φ) : φ := ◇p ↔ ¬□¬p
def ax_T (p : φ) : φ := □p → p
def ax_B (p : φ) : φ := p → □(◇p)
def ax_4 (p : φ) : φ := □p → □(□p)
def ax_5 (p : φ) : φ := ◇p → □(◇p)
def ax_M (p q : φ) : φ := □(p∧q) ↔ □p

def ax_K (p q : φ) : φ := □(p → q) → (□p → □q)
def ax_K_b (p q : φ) : φ := ax_K p q
def ax_K_d (p q : φ) : φ := ◇(p → q) → (◇p → ◇q)
def ax_N : φ := □⊤
def ax_N_b : φ := ax_N
def ax_N_d : φ := ◇⊤
def ax_KN2 (p q : φ) : φ := ((ax_K_b p q) ∧ ax_N_b) ∨ ((ax_K_d p q) ∧ ax_N_d)

end ModalAxioms
