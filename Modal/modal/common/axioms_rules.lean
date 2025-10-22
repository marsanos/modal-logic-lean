import Modal.modal.common.syntax
import Modal.common.inference_rule


namespace Modal.Rules

variable {Form : Type} [Modal.Syntax Form]

def re (φ ψ : Form) : InferenceRule Form := ⟨φ ↔ ψ, □φ ↔ □ψ⟩
def nec (φ : Form)  : InferenceRule Form := ⟨φ, □φ⟩

end Modal.Rules


namespace Modal.Axioms

variable {Form : Type} [Modal.Syntax Form]

def m (φ ψ : Form) : Form := □(φ∧ψ) → □φ
def k (φ ψ : Form) : Form := □(φ → ψ) → (□φ → □ψ)
def n : Form := □⊤

-- the following are correct definitions, but not needed as yet
--def t (φ : Form) : Form := □φ → φ
--def four (φ : Form) : Form := □φ → □(□φ)
--def five (φ : Form) : Form := ◇φ → □(◇φ)
--def b (φ : Form) : Form := φ → □(◇φ)

end Modal.Axioms
