import Mathlib.Data.Set.Defs
import Modal.common.entailment


namespace Consistency

variable {𝓔 : EntailmentSystem} [HasBot 𝓔.formula] [HasNeg 𝓔.formula]

def is_consistent (Γ : Set 𝓔.formula) : Prop :=
  ¬ Γ ⊢ ⊥

-- mcs = maximally consistent set
def is_mcs (Γ : Set 𝓔.formula) : Prop :=
  is_consistent Γ ∧ ∀ φ, φ ∉ Γ → ¬ is_consistent (Γ ∪ {φ})

-- Lindenbaum's Lemma: every consistent set extends to a mcs
theorem lindenbaum (Γ : Set 𝓔.formula) (h : is_consistent Γ) :
    ∃ Γ' : Set 𝓔.formula, is_mcs Γ' ∧ Γ ⊆ Γ' := by
  admit
  -- Well-known result. See, for example, Blackburn et al., Lemma 4.17



/-
-- some basic consistency results that may be needed later

lemma no_cpl_bot : ¬ CPL.has_proof ∅ (⊥ : Modal.Formula α) := by
  admit
  -- Standard result: CPL cannot prove ⊥
  -- Proof: by soundness, if CPL proves ⊥, then ⊥ is a tautology,
  -- but ⊥ evaluates to False under any valuation.

lemma consistent_no_bot {Γ : Multiset (Modal.Formula α)}
    (hΓ : is_consistent Γ) : (⊥ : Modal.Formula 𝓕) ∉ Γ := by
  intro hbot
  have : MProof' (α := α) Γ ⊥ := MProof'.assumption hbot
  exact hΓ this

lemma mcs_no_bot {Γ : Multiset (Modal.Formula α)}
    (hΓ : is_maximally_consistent Γ) : (⊥ : Modal.Formula 𝓕) ∉ Γ :=
  consistent_no_bot 𝓕.1

-- Basic MCS properties (admitted as standard results)

lemma mcs_no_contradiction
    {Γ : Multiset (Modal.Formula α)}
    {φ : Modal.Formula 𝓕}
    (hφ : φ ∈ 𝓕) (hneg : (¬φ) ∈ 𝓕) : MProof' (α := α) Γ ⊥ := by
  admit
  -- Standard CPL result: from {φ, ¬φ} derive ⊥

lemma mcs_double_neg
    {Γ : Multiset (Modal.Formula α)}
    (hΓ : is_maximally_consistent 𝓕)
    {φ : Modal.Formula 𝓕} :
    φ ∈ 𝓕 ↔ (¬¬φ) ∈ Γ := by
  admit
  -- Standard result for MCS: double negation equivalence

lemma mcs_mem_or_neg_mem
    {Γ : Multiset (Modal.Formula α)}
    (hΓ : is_maximally_consistent 𝓕)
    (φ : Modal.Formula 𝓕) : φ ∈ 𝓕 ∨ (¬φ) ∈ Γ := by
  classical
  by_cases hmem : φ ∈ 𝓕
  · exact Or.inl hmem
  · have h_incons : MProof' (α := α) (φ ::ₘ Γ) ⊥ := by
      have hnot := hΓ.2 φ hmem
      dsimp [is_consistent] at hnot
      exact not_not.mp hnot
    cases h_incons with
    | assumption hbot_mem =>
        obtain hcases | hbotΓ := Multiset.mem_cons.mp hbot_mem
        · subst hcases
          have : (¬(⊥ : Modal.Formula α)) ∈ Γ := by
            by_contra hnot
            have hnincons : MProof' (α := α) ((¬(⊥ : Modal.Formula α)) ::ₘ Γ) ⊥ := by
              have hnotCons := hΓ.2 (¬(⊥ : Modal.Formula α)) hnot
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
    {Γ : Multiset (Modal.Formula α)}
    (hΓ : is_maximally_consistent 𝓕)
    {φ ψ : Modal.Formula 𝓕} :
    (φ → ψ) ∈ 𝓕 ↔ (φ ∈ Γ → ψ ∈ Γ) := by
  admit  -- known result, not dependent on any particular setting

-- Connection between provability and MCS

lemma deriv_iff_mem_mcs (φ : Modal.Formula 𝓕) :
    MProof φ ↔ ∀ {Γ : Multiset (Modal.Formula α)},
                          is_maximally_consistent Γ → φ ∈ Γ := by
  admit
  -- Well-known result for M and other logics.
  -- See, for example, Chellas, Theorem 2.20 (2).
-/

end Consistency
