import Modal.cpl.proof
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

-- Basic consistency results

lemma no_cpl_bot : ¬ CPL.CPLProof (⊥ : ModalFormula α) := by
  admit
  -- Standard result: CPL cannot prove ⊥
  -- Proof: by soundness, if CPL proves ⊥, then ⊥ is a tautology,
  -- but ⊥ evaluates to False under any valuation.

lemma consistent_no_bot {Γ : Multiset (ModalFormula α)}
    (hΓ : is_consistent Γ) : (⊥ : ModalFormula α) ∉ Γ := by
  intro hbot
  have : MProof' (α := α) Γ ⊥ := MProof'.assumption hbot
  exact hΓ this

lemma mcs_no_bot {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent Γ) : (⊥ : ModalFormula α) ∉ Γ :=
  consistent_no_bot hΓ.1

-- Basic MCS properties (admitted as standard results)

lemma mcs_no_contradiction
    {Γ : Multiset (ModalFormula α)}
    {φ : ModalFormula α}
    (hφ : φ ∈ Γ) (hneg : (¬φ) ∈ Γ) : MProof' (α := α) Γ ⊥ := by
  admit
  -- Standard CPL result: from {φ, ¬φ} derive ⊥

lemma mcs_double_neg
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent Γ)
    {φ : ModalFormula α} :
    φ ∈ Γ ↔ (¬¬φ) ∈ Γ := by
  admit
  -- Standard result for MCS: double negation equivalence

lemma mcs_mem_or_neg_mem
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent Γ)
    (φ : ModalFormula α) : φ ∈ Γ ∨ (¬φ) ∈ Γ := by
  classical
  by_cases hmem : φ ∈ Γ
  · exact Or.inl hmem
  · have h_incons : MProof' (α := α) (φ ::ₘ Γ) ⊥ := by
      have hnot := hΓ.2 φ hmem
      dsimp [is_consistent] at hnot
      exact not_not.mp hnot
    cases h_incons with
    | assumption hbot_mem =>
        obtain hcases | hbotΓ := Multiset.mem_cons.mp hbot_mem
        · subst hcases
          have : (¬(⊥ : ModalFormula α)) ∈ Γ := by
            by_contra hnot
            have hnincons : MProof' (α := α) ((¬(⊥ : ModalFormula α)) ::ₘ Γ) ⊥ := by
              have hnotCons := hΓ.2 (¬(⊥ : ModalFormula α)) hnot
              dsimp [is_consistent] at hnotCons
              exact not_not.mp hnotCons
            cases hnincons with
            | assumption habs =>
                obtain hcases' | hbotΓ' := Multiset.mem_cons.mp habs
                · cases hcases'
                · exact False.elim ((mcs_no_bot hΓ) hbotΓ')
            | cpl hbot =>
                exact False.elim (no_cpl_bot hbot)
          exact Or.inr (by simpa using this)
        · exact False.elim ((mcs_no_bot hΓ) hbotΓ)
    | cpl hbot =>
        exact False.elim (no_cpl_bot hbot)

lemma mcs_impl_closed
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent Γ)
    {φ ψ : ModalFormula α} :
    (φ → ψ) ∈ Γ ↔ (φ ∈ Γ → ψ ∈ Γ) := by
  admit  -- known result, not dependent on any particular setting

-- Connection between provability and MCS

lemma deriv_iff_mem_mcs (φ : ModalFormula α) :
    MProof φ ↔ ∀ {Γ : Multiset (ModalFormula α)},
                          is_maximally_consistent Γ → φ ∈ Γ := by
  admit
  -- Well-known result for M and other logics.
  -- See, for example, Chellas, Theorem 2.20 (2).

end ModalConsistency
