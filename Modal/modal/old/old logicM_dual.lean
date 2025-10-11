import Modal.modal.formula
import Modal.modal.models.dual
import Modal.modal.logics.logic_M
import Modal.modal.axioms_rules
import Modal.modal.consistency
import Modal.cpl.metatheorems


open ModalFormula Dual ModalAxioms ModalRules CPLSeq CPLMetatheorems ModalConsistency


variable {α : Type}

section soundness
-- Helper lemma: world_sat at a fixed world is a classical valuation
def world_as_valuation (m : Dual.Model α) (w : m.frame.world) :
    CPLMetatheorems.Valuation (ModalFormula α) where
  eval := world_sat m w
  eval_bot := rfl
  eval_impl _ _ := rfl

-- Helper lemma: CPL tautologies are valid in dual models
-- This follows immediately from CPL soundness: CPL proofs give tautologies,
-- and world_sat at each world is a classical valuation.
lemma cpl_valid (φ : ModalFormula α) (h : CPLSeq.CPLProof φ) : valid φ := by
  intro f val w
  have h_taut := CPLMetatheorems.cpl_sound h
  unfold CPLMetatheorems.is_tautology at h_taut
  exact h_taut (world_as_valuation ⟨f, val⟩ w)

-- Helper lemma: ax_dia is valid
lemma ax_dia_valid (p : ModalFormula α) : valid (ax_dia p) := by
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

-- Helper lemma: ax_m is valid
lemma ax_m_valid (p q : ModalFormula α) : valid (ax_m p q) := by
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

-- Helper lemma: rl_re preserves validity
lemma rl_re_valid (p q : ModalFormula α) (h : valid (p ↔ q)) : valid (□p ↔ □q) := by
  intro f val w
  rw [world_sat_iff]
  cases w with
  | inl wn =>
    simp only [world_sat]
    constructor
    · intro hp_box v hrel
      have hiff := h f val v
      rw [world_sat_iff] at hiff
      exact hiff.mp (hp_box v hrel)
    · intro hq_box v hrel
      have hiff := h f val v
      rw [world_sat_iff] at hiff
      exact hiff.mpr (hq_box v hrel)
  | inr wp =>
    simp only [world_sat]
    constructor
    · intro ⟨v, hrel, hp⟩
      have hiff := h f val v
      rw [world_sat_iff] at hiff
      exact ⟨v, hrel, hiff.mp hp⟩
    · intro ⟨v, hrel, hq⟩
      have hiff := h f val v
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

-- Type of maximally consistent sets
abbrev MCS (α : Type) := { Γ : Set (ModalFormula α) // MaximallyConsistent Γ }

-- Canonical accessibility relation
-- The relation is the same regardless of the Boolean mark,
-- based on the box formulas in the source MCS
def canonical_rel (α : Type) :
    (MCS α ⊕ MCS α) → (MCS α ⊕ MCS α) → Prop :=
  fun w₁ w₂ =>
    let Γ₁ := match w₁ with | .inl ⟨Γ, _⟩ => Γ | .inr ⟨Γ, _⟩ => Γ
    let Γ₂ := match w₂ with | .inl ⟨Γ, _⟩ => Γ | .inr ⟨Γ, _⟩ => Γ
    ∀ φ : ModalFormula α, (□φ) ∈ Γ₁ → φ ∈ Γ₂

-- Canonical frame: worlds are pairs (MCS, Boolean mark)
-- Each MCS appears twice: once as n-world, once as p-world
def CanonicalFrame (α : Type) : Dual.Frame where
  n_world := MCS α  -- n-worlds (necessity worlds): MCS with n-mark
  p_world := MCS α  -- p-worlds (possibility worlds): MCS with p-mark
  rel := canonical_rel α  -- Standard canonical relation

-- Canonical model: canonical frame with valuation based on atomic formulas
def CanonicalModel (α : Type) : Dual.Model α where
  frame := CanonicalFrame α
  val w a := match w with
    | .inl ⟨Γ, _⟩ => (ModalFormula.atom a) ∈ Γ  -- In n-world (necessity world)
    | .inr ⟨Γ, _⟩ => (ModalFormula.atom a) ∈ Γ  -- In p-world (possibility world)

-- Helper to extract the underlying MCS from a world
def world_to_set {α : Type} (w : (CanonicalModel α).frame.world) :
    Set (ModalFormula α) :=
  match w with
  | .inl ⟨Γ, _⟩ => Γ
  | .inr ⟨Γ, _⟩ => Γ

-- Truth Lemma: a formula is in a world iff it's satisfied at that world
theorem truth_lemma :
    ∀ (φ : ModalFormula α) (w : (CanonicalModel α).frame.world),
    φ ∈ world_to_set w ↔ world_sat (CanonicalModel α) w φ := by
  intro φ w
  induction φ generalizing w with
  | atom a =>
    -- Base case: atomic formula
    cases w with
    | inl wn =>
      -- n-world (necessity world)
      unfold world_to_set world_sat
      simp [CanonicalModel]
      rfl
    | inr wp =>
      -- p-world (possibility world)
      unfold world_to_set world_sat
      simp [CanonicalModel]
      rfl
  | bot =>
    -- Case for ⊥
    cases w with
    | inl wn =>
      unfold world_to_set world_sat
      constructor
      · intro h
        -- If ⊥ ∈ Γ, but Γ is maximally consistent, contradiction
        have ⟨Γ, hΓ⟩ := wn
        exact absurd h (ModalConsistency.mcs_not_bot Γ hΓ)
      · intro h
        exact False.elim h
    | inr wp =>
      unfold world_to_set world_sat
      constructor
      · intro h
        -- If ⊥ ∈ Γ, but Γ is maximally consistent, contradiction
        have ⟨Γ, hΓ⟩ := wp
        exact absurd h (ModalConsistency.mcs_not_bot Γ hΓ)
      · intro h
        exact False.elim h
  | impl φ ψ ih_φ ih_ψ =>
    -- Case for φ → ψ
    cases w with
    | inl wn =>
      unfold world_to_set world_sat
      constructor
      · intro h hφ
        -- If (φ → ψ) ∈ Γ, then world_sat w φ → world_sat w ψ
        -- By IH, φ ∈ Γ follows from world_sat w φ
        have ⟨Γ, hΓ⟩ := wn
        rw [← ih_φ (.inl ⟨Γ, hΓ⟩)] at hφ
        -- Now we have φ ∈ Γ and (φ → ψ) ∈ Γ, so by modus ponens, ψ ∈ Γ
        have hψ : ψ ∈ Γ := ModalConsistency.mcs_modus_ponens Γ hΓ φ ψ h hφ
        rw [← ih_ψ (.inl ⟨Γ, hΓ⟩)]
        exact hψ
      · intro h
        -- If world_sat w φ → world_sat w ψ, then (φ → ψ) ∈ Γ
        -- By maximality, either (φ → ψ) ∈ Γ or ¬(φ → ψ) ∈ Γ
        have ⟨Γ, hΓ⟩ := wn
        -- Use maximal_consistent_closed to get (φ → ψ) ∈ Γ or ¬(φ → ψ) ∈ Γ
        cases ModalConsistency.maximal_consistent_closed Γ hΓ (φ → ψ) with
        | inl himpl =>
          -- (φ → ψ) ∈ Γ, we're done
          exact himpl
        | inr hnotimpl =>
          -- ¬(φ → ψ) ∈ Γ
          -- From ¬(φ → ψ) we can derive φ ∧ ¬ψ (classically)
          have ⟨hφ, hnotψ⟩ := ModalConsistency.mcs_not_impl_components Γ hΓ φ ψ hnotimpl
          -- We have φ ∈ Γ, so world_sat w φ by IH
          have hwφ : world_sat (CanonicalModel α) (.inl ⟨Γ, hΓ⟩) φ := by
            rw [← ih_φ (.inl ⟨Γ, hΓ⟩)]
            exact hφ
          -- By h, we get world_sat w ψ
          have hwψ := h hwφ
          -- By IH, ψ ∈ Γ
          rw [← ih_ψ (.inl ⟨Γ, hΓ⟩)] at hwψ
          -- But we also have ¬ψ ∈ Γ, which means ψ ∉ Γ
          have hnotψmem : ψ ∉ Γ := by
            intro hψ
            -- If ψ ∈ Γ and ¬ψ ∈ Γ, this violates consistency
            exact ModalConsistency.mcs_not_both Γ hΓ ψ hψ hnotψ
          -- Contradiction
          exact absurd hwψ hnotψmem
    | inr wp =>
      unfold world_to_set world_sat
      constructor
      · intro h hφ
        -- Same as n-world case
        have ⟨Γ, hΓ⟩ := wp
        rw [← ih_φ (.inr ⟨Γ, hΓ⟩)] at hφ
        have hψ : ψ ∈ Γ := ModalConsistency.mcs_modus_ponens Γ hΓ φ ψ h hφ
        rw [← ih_ψ (.inr ⟨Γ, hΓ⟩)]
        exact hψ
      · intro h
        -- Same as n-world case
        have ⟨Γ, hΓ⟩ := wp
        cases ModalConsistency.maximal_consistent_closed Γ hΓ (φ → ψ) with
        | inl himpl =>
          exact himpl
        | inr hnotimpl =>
          have ⟨hφ, hnotψ⟩ := ModalConsistency.mcs_not_impl_components Γ hΓ φ ψ hnotimpl
          have hwφ : world_sat (CanonicalModel α) (.inr ⟨Γ, hΓ⟩) φ := by
            rw [← ih_φ (.inr ⟨Γ, hΓ⟩)]
            exact hφ
          have hwψ := h hwφ
          rw [← ih_ψ (.inr ⟨Γ, hΓ⟩)] at hwψ
          have hnotψmem : ψ ∉ Γ := by
            intro hψ
            exact ModalConsistency.mcs_not_both Γ hΓ ψ hψ hnotψ
          exact absurd hwψ hnotψmem
  | box φ ih =>
    -- Case for □φ
    cases w with
    | inl wn =>
      -- At n-world: □φ has universal semantics (∀-semantics)
      unfold world_to_set world_sat
      simp [CanonicalModel, CanonicalFrame, canonical_rel]
      constructor
      · intro h v hrel
        -- If □φ ∈ Γ and Γ R Δ, then φ ∈ Δ by definition of canonical_rel
        -- Then use IH at v
        have ⟨Γ, hΓ⟩ := wn
        have hφ_in_Δ : φ ∈ world_to_set v := hrel φ h
        rw [ih v] at hφ_in_Δ
        exact hφ_in_Δ
      · intro h
        -- If ∀v, Γ R v → world_sat v φ, then □φ ∈ Γ
        -- Use mcs_box_of_all
        have ⟨Γ, hΓ⟩ := wn
        apply ModalConsistency.mcs_box_of_all Γ hΓ φ
        intro Δ hΔ hrel
        -- We need to show φ ∈ Δ
        -- We have h : ∀v, canonical_rel Γ Δ' → world_sat v φ (where v comes from Δ')
        -- We can construct v = .inl ⟨Δ, hΔ⟩ and show canonical_rel holds
        have hsat := h (.inl ⟨Δ, hΔ⟩) hrel
        have := ih (.inl ⟨Δ, hΔ⟩)
        exact this.mpr hsat
    | inr wp =>
      -- At p-world: □φ has existential semantics (∃-semantics)
      unfold world_to_set world_sat
      simp [CanonicalModel, CanonicalFrame, canonical_rel]
      constructor
      · intro h
        -- If □φ ∈ Γ, then ∃v, Γ R v ∧ world_sat v φ
        have ⟨Γ, hΓ⟩ := wp
        -- Use mcs_box_exists to get a witness MCS
        have ⟨Δ, hΔ, hrel, hφ⟩ := ModalConsistency.mcs_box_exists Γ hΓ φ h
        -- We can use either .inl or .inr for the witness; let's use .inl
        use .inl ⟨Δ, hΔ⟩
        constructor
        · exact hrel
        · have := ih (.inl ⟨Δ, hΔ⟩)
          exact this.mp hφ
      · intro ⟨v, hrel, hsat⟩
        -- If ∃v, Γ R v ∧ world_sat v φ, then □φ ∈ Γ
        -- Use mcs_box_of_exists
        have ⟨Γ, hΓ⟩ := wp
        apply ModalConsistency.mcs_box_of_exists Γ hΓ φ
        -- We need to provide the witness
        cases v with
        | inl vn =>
          have ⟨Δ, hΔ⟩ := vn
          use Δ, hΔ, hrel
          have := ih (.inl ⟨Δ, hΔ⟩)
          exact this.mpr hsat
        | inr vp =>
          have ⟨Δ, hΔ⟩ := vp
          use Δ, hΔ, hrel
          have := ih (.inr ⟨Δ, hΔ⟩)
          exact this.mpr hsat
  | dia φ ih =>
    -- Case for ◇φ
    cases w with
    | inl wn =>
      -- At n-world: ◇φ has existential semantics (∃-semantics)
      unfold world_to_set world_sat
      simp [CanonicalModel, CanonicalFrame, canonical_rel]
      constructor
      · intro h
        -- If ◇φ ∈ Γ, then ∃v, Γ R v ∧ world_sat v φ
        have ⟨Γ, hΓ⟩ := wn
        -- Use mcs_dia_exists to get a witness MCS
        have ⟨Δ, hΔ, hrel, hφ⟩ := ModalConsistency.mcs_dia_exists Γ hΓ φ h
        -- We can use either .inl or .inr for the witness; let's use .inl
        use .inl ⟨Δ, hΔ⟩
        constructor
        · exact hrel
        · have := ih (.inl ⟨Δ, hΔ⟩)
          exact this.mp hφ
      · intro ⟨v, hrel, hsat⟩
        -- If ∃v, Γ R v ∧ world_sat v φ, then ◇φ ∈ Γ
        -- Use mcs_dia_of_exists
        have ⟨Γ, hΓ⟩ := wn
        apply ModalConsistency.mcs_dia_of_exists Γ hΓ φ
        cases v with
        | inl vn =>
          have ⟨Δ, hΔ⟩ := vn
          use Δ, hΔ, hrel
          have := ih (.inl ⟨Δ, hΔ⟩)
          exact this.mpr hsat
        | inr vp =>
          have ⟨Δ, hΔ⟩ := vp
          use Δ, hΔ, hrel
          have := ih (.inr ⟨Δ, hΔ⟩)
          exact this.mpr hsat
    | inr wp =>
      -- At p-world: ◇φ has universal semantics (∀-semantics)
      unfold world_to_set world_sat
      simp [CanonicalModel, CanonicalFrame, canonical_rel]
      constructor
      · intro h v hrel
        -- If ◇φ ∈ Γ and Γ R Δ, then φ ∈ Δ
        -- Use mcs_dia_all: ◇φ ∈ Γ implies φ holds at all accessible worlds
        have ⟨Γ, hΓ⟩ := wp
        cases v with
        | inl vn =>
          have ⟨Δ, hΔ⟩ := vn
          have hφ := ModalConsistency.mcs_dia_all Γ hΓ φ h Δ hΔ hrel
          have := ih (.inl ⟨Δ, hΔ⟩)
          exact this.mp hφ
        | inr vp =>
          have ⟨Δ, hΔ⟩ := vp
          have hφ := ModalConsistency.mcs_dia_all Γ hΓ φ h Δ hΔ hrel
          have := ih (.inr ⟨Δ, hΔ⟩)
          exact this.mp hφ
      · intro h
        -- If ∀v, Γ R v → world_sat v φ, then ◇φ ∈ Γ
        -- Use mcs_dia_of_all
        have ⟨Γ, hΓ⟩ := wp
        apply ModalConsistency.mcs_dia_of_all Γ hΓ φ
        intro Δ hΔ hrel
        have hsat := h (.inl ⟨Δ, hΔ⟩) hrel
        have := ih (.inl ⟨Δ, hΔ⟩)
        exact this.mpr hsat

-- Completeness: if φ is valid, then φ is provable
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
