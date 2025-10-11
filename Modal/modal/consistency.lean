import Modal.modal.formula
import Modal.modal.logics.logic_M

namespace ModalConsistency

open ModalFormula

variable {α : Type}

def is_consistent (Γ : Multiset (ModalFormula α)) : Prop :=
  ¬ MProof' (α:=α) Γ ⊥

def is_maximally_consistent (Γ : Multiset (ModalFormula α)) : Prop :=
  is_consistent Γ ∧ ∀ φ, φ ∉ Γ → ¬is_consistent (φ ::ₘ Γ)

-- Lindenbaum's Lemma: every consistent set extends to a maximally consistent set
theorem lindenbaum
    (Γ : Multiset (ModalFormula α)) (h : is_consistent Γ) :
    ∃ Γ' : Multiset (ModalFormula α), is_maximally_consistent Γ' ∧ Γ ⊆ Γ' := by
  admit
  -- Well-known result. See Blackburn et al., Lemma 4.17

end ModalConsistency
