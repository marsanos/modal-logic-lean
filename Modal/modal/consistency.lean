import Modal.modal.formula
import Modal.modal.logics.logic_M

namespace ModalConsistency

open ModalFormula

variable {α : Type}

-- A set of formulas is consistent with respect to MProof if we cannot derive
-- a contradiction from it
def Consistent (Γ : Set (ModalFormula α)) : Prop :=
  ¬∃ (φ : ModalFormula α), (∀ ψ ∈ Γ, MProof ψ) → MProof φ ∧ MProof (¬φ)

-- A set is maximally consistent if it's consistent and no proper superset is consistent
def MaximallyConsistent (Γ : Set (ModalFormula α)) : Prop :=
  Consistent Γ ∧ ∀ φ, φ ∉ Γ → ¬Consistent (Γ ∪ {φ})

end ModalConsistency
