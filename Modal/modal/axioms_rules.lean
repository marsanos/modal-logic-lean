/- The type 𝓕 (backslash MCF) is supposed to be the type of modal formulas,
but this works for anything with the appropriate syntax. -/


import Modal.modal.syntax
import Modal.common.inference


namespace Modal.Rules

variable {𝓕 : Type} [Modal.Syntax 𝓕]

def rl_re (φ ψ : 𝓕) : InferenceRule 𝓕 := ⟨φ ↔ ψ, □φ ↔ □ψ⟩
def rl_nec (φ : 𝓕)  : InferenceRule 𝓕 := ⟨φ, □φ⟩

end Modal.Rules


namespace Modal.Axioms

variable {𝓕 : Type} [Modal.Syntax 𝓕]

def ax_m (φ ψ : 𝓕) : 𝓕 := □(φ∧ψ) → □φ
def ax_k (φ ψ : 𝓕) : 𝓕 := □(φ → ψ) → (□φ → □ψ)
def ax_n : 𝓕           := □⊤
--def ax_t (φ : 𝓕) : 𝓕   := □φ → φ
--def ax_4 (φ : 𝓕) : 𝓕   := □φ → □(□φ)
--def ax_5 (φ : 𝓕) : 𝓕   := ◇φ → □(◇φ)
--def ax_b (φ : 𝓕) : 𝓕   := φ → □(◇φ)

end Modal.Axioms
