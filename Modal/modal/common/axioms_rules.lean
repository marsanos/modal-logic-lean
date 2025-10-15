/- The type 𝓕 (backslash MCF) is supposed to be the type of modal formulas,
but this works for anything with the appropriate syntax. -/


import Modal.modal.common.syntax
import Modal.common.inference


namespace Modal.Rules

variable {𝓕 : Type} [Modal.Syntax 𝓕]

def re (φ ψ : 𝓕) : InferenceRule 𝓕 := ⟨φ ↔ ψ, □φ ↔ □ψ⟩
def nec (φ : 𝓕)  : InferenceRule 𝓕 := ⟨φ, □φ⟩

end Modal.Rules


namespace Modal.Axioms

variable {𝓕 : Type} [Modal.Syntax 𝓕]

def m (φ ψ : 𝓕) : 𝓕 := □(φ∧ψ) → □φ
def k (φ ψ : 𝓕) : 𝓕 := □(φ → ψ) → (□φ → □ψ)
def n : 𝓕           := □⊤

-- the following are correct, but not needed as yet
--def t (φ : 𝓕) : 𝓕   := □φ → φ
--def four (φ : 𝓕) : 𝓕   := □φ → □(□φ)
--def five (φ : 𝓕) : 𝓕   := ◇φ → □(◇φ)
--def b (φ : 𝓕) : 𝓕   := φ → □(◇φ)

end Modal.Axioms
