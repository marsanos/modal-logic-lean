import Modal.modal.formula
import Modal.modal.models.dual
import Modal.modal.axioms_rules
import Modal.modal.consistency
import Modal.cpl.metatheorems


open ModalFormula Dual ModalAxioms ModalRules


variable {α : Type}

section soundness

-- each world contains a valuation - this function extracts it
def world_as_valuation (m : Dual.Model α) (w : m.frame.world) :
    CPLMetatheorems.Valuation (ModalFormula α) where
  eval := world_sat m w
  eval_bot := rfl
  eval_impl _ _ := rfl

-- So that the proof is not too long, we prove some helper lemmas first.

-- CPL tautologies are valid in dual models
lemma cpl_valid (φ : ModalFormula α) (h : CPLSeq.CPLProof φ) : Dual.valid φ := by
  intro f val w
  have h_taut := CPLMetatheorems.cpl_sound h
  unfold CPLMetatheorems.is_tautology at h_taut
  exact h_taut (world_as_valuation ⟨f, val⟩ w)

lemma ax_dia_valid (φ : ModalFormula α) : Dual.valid (ax_dia φ) := by
  intro f val w
  unfold ax_dia
  rw [world_sat_iff]
  cases w with
  | inl wn =>
    -- At n-world: ◇p ↔ ∃v, R(wn,v) ∧ p@v
    --             ¬□¬p ↔ ¬(∀v, R(wn,v) → ¬p@v) ↔ ∃v, R(wn,v) ∧ p@v
    simp only [world_sat, world_sat_neg]
    constructor
    · intro ⟨v, hrel, hp⟩ hall
      exact hall v hrel hp
    · intro h
      by_contra hneg
      push_neg at hneg
      exact h hneg
  | inr wp =>
    -- At p-world: ◇p ↔ ∀v, R(wp,v) → p@v
    --             ¬□¬p ↔ ¬(∃v, R(wp,v) ∧ ¬p@v) ↔ ∀v, R(wp,v) → p@v
    simp only [world_sat, world_sat_neg]
    constructor
    · intro hall ⟨v, hrel, hnp⟩
      exact hnp (hall v hrel)
    · intro h v hrel
      by_contra hnp
      exact h ⟨v, hrel, hnp⟩

lemma ax_m_valid (φ ψ : ModalFormula α) : Dual.valid (ax_m φ ψ) := by
  intro f val w
  unfold ax_m world_sat
  cases w with
  | inl wn =>
    -- At n-world: □(p∧q) → □p
    intro h v hrel
    have hpq := h v hrel
    rw [world_sat_and] at hpq
    exact hpq.1
  | inr wp =>
    -- At p-world: □(p∧q) → □p
    intro ⟨v, hrel, hpq⟩
    rw [world_sat_and] at hpq
    exact ⟨v, hrel, hpq.1⟩

lemma rl_re_valid (φ ψ : ModalFormula α) (h : Dual.valid (rl_re φ ψ).premise) :
    Dual.valid (rl_re φ ψ).conclusion := by
  intro f val w
  rw [rl_re]
  rw [world_sat_iff]
  cases w with
  | inl wn =>
    simp only [world_sat]
    constructor
    · intro hp_box v hrel
      have hiff := h f val v
      rw [rl_re] at hiff
      rw [world_sat_iff] at hiff
      exact hiff.mp (hp_box v hrel)
    · intro hq_box v hrel
      have hiff := h f val v
      rw [rl_re] at hiff
      rw [world_sat_iff] at hiff
      exact hiff.mpr (hq_box v hrel)
  | inr wp =>
    simp only [world_sat]
    constructor
    · intro ⟨v, hrel, hp⟩
      have hiff := h f val v
      rw [rl_re] at hiff
      rw [world_sat_iff] at hiff
      exact ⟨v, hrel, hiff.mp hp⟩
    · intro ⟨v, hrel, hq⟩
      have hiff := h f val v
      rw [rl_re] at hiff
      rw [world_sat_iff] at hiff
      exact ⟨v, hrel, hiff.mpr hq⟩

theorem logicM_dual_sound :
    ∀ (φ : ModalFormula α), MProof φ → valid φ := by
    intro φ hproof
    induction hproof with
    | cpl h_cpl => exact cpl_valid _ h_cpl
    | ax_dia => exact ax_dia_valid _
    | ax_m => exact ax_m_valid _ _
    | rl_re h_prem ih => exact rl_re_valid _ _ ih

end soundness


section completeness

theorem logicM_dual_complete :
    ∀ (φ : ModalFormula α), valid φ → MProof φ := by
    sorry

end completeness


theorem logicM_dual_sc :
    ∀ (φ : ModalFormula α), valid φ ↔ MProof φ := by
    intro φ
    constructor
    · exact logicM_dual_complete φ
    · exact logicM_dual_sound φ
