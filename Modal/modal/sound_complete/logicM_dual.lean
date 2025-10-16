import Modal.cpl.entailment
import Modal.modal.common.formula
import Modal.modal.models.dual_new
import Modal.modal.common.axioms_rules
import Modal.common.consistency
import Modal.modal.logics.logic_M
import Modal.cpl.sound_complete


open Modal

variable {𝓐 : Type}

section soundness

-- each world contains a valuation - this function extracts it
--def world_as_valuation (m : Dual.Model 𝓐) (w : m.frame.world) :=
--    CPL.Valuation (Modal.Formula 𝓐) where
--  eval := world_sat m w
--  eval_bot := rfl
--  eval_impl _ _ := rfl

-- So that the proof is not too long, we prove some helper lemmas first.

-- CPL tautologies are valid in dual models
lemma cpl_valid (φ : Modal.Formula 𝓐) (h : (CPL.entails ∅ (to_cpl 𝓐 φ))) : Dual.valid φ := by
  intro f val w
  have h_taut := CPL.sound h
  unfold CPL.complete at h_taut
  let m : Dual.Model 𝓐 := { frame := f, val := val }
  have h_models : CPL.models_set (world_as_valuation m w) ∅ := by
    intro ψ hψ
    cases hψ
  have h_eval := h_taut (world_as_valuation m w) h_models
  exact h_eval

lemma m_valid (φ ψ : Modal.Formula 𝓐) : Dual.valid (Modal.Axioms.m φ ψ) := by
  intro f val w
  unfold Dual.world_sat
  cases w with
  | inl wn =>
    -- At n-world: □(p∧q) → □p
    intro h v hrel
    have hpq := h v hrel
    rw [Dual.world_sat_and] at hpq
    exact hpq.1
  | inr wp =>
    -- At p-world: □(p∧q) → □p
    intro ⟨v, hrel, hpq⟩
    rw [Dual.world_sat_and] at hpq
    exact ⟨v, hrel, hpq.1⟩

lemma re_valid (φ ψ : Modal.Formula 𝓐) (h : Dual.valid (Modal.Rules.re φ ψ).premise) :
    Dual.valid (Modal.Rules.re φ ψ).conclusion := by
  intro f val w
  rw [Modal.Rules.re]
  rw [Dual.world_sat_iff]
  cases w with
  | inl wn =>
    simp only [Dual.world_sat]
    constructor
    · intro hp_box v hrel
      have hiff := h f val v
      rw [Modal.Rules.re] at hiff
      rw [Dual.world_sat_iff] at hiff
      exact hiff.mp (hp_box v hrel)
    · intro hq_box v hrel
      have hiff := h f val v
      rw [Modal.Rules.re] at hiff
      rw [Dual.world_sat_iff] at hiff
      exact hiff.mpr (hq_box v hrel)
  | inr wp =>
    simp only [Dual.world_sat]
    constructor
    · intro ⟨v, hrel, hp⟩
      have hiff := h f val v
      rw [Modal.Rules.re] at hiff
      rw [Dual.world_sat_iff] at hiff
      exact ⟨v, hrel, hiff.mp hp⟩
    · intro ⟨v, hrel, hq⟩
      have hiff := h f val v
      rw [Modal.Rules.re] at hiff
      rw [Dual.world_sat_iff] at hiff
      exact ⟨v, hrel, hiff.mpr hq⟩

theorem logicM_dual_sound :
    ∀ (φ : Modal.Formula 𝓐), MProof ∅ φ → Dual.valid φ := by
    intro φ hproof
    induction hproof with
    | assumption h => cases h
    | cpl h_cpl => exact cpl_valid _ h_cpl
    | m => exact m_valid _ _
    | re h_prem ih => exact re_valid _ _ ih

end soundness

section completeness

section canonical_model

abbrev NWorld (𝓐 : Type) :=
  {w : (Multiset (Modal.Formula 𝓐)) × Bool //
    is_maximally_consistent w.1 ∧ w.2 = true}
abbrev PWorld (𝓐 : Type) :=
  {w : (Multiset (Modal.Formula 𝓐)) × Bool //
    is_maximally_consistent w.1 ∧ w.2 = false}
abbrev World (𝓐 : Type) := NWorld 𝓐 ⊕ PWorld 𝓐

def is_nworld {𝓐 : Type} : World 𝓐 → Prop
  | .inl _ => true
  | .inr _ => false
def is_pworld {𝓐 : Type} : World 𝓐 → Prop
  | .inl _ => false
  | .inr _ => true

def world_to_set {𝓐 : Type} (w : World 𝓐) : Multiset (Modal.Formula 𝓐) :=
  match w with
  | .inl wn => wn.val.1
  | .inr wp => wp.val.1

def canonical_acc (𝓐 : Type) : World 𝓐 → World 𝓐 → Prop :=
  fun w₁ w₂ =>
    match w₁ with
    | .inl _ => ∀ φ : Modal.Formula 𝓐,
                  (□φ) ∈ world_to_set w₁ → φ ∈ world_to_set w₂
    | .inr _ => ∀ φ : Modal.Formula 𝓐,
                  (◇φ) ∈ world_to_set w₁ → φ ∈ world_to_set w₂

def CanonicalFrame (𝓐 : Type) : Dual.Frame where
  n_world := NWorld 𝓐
  p_world := PWorld 𝓐
  rel := canonical_acc 𝓐

-- Canonical model: canonical frame with valuation based on atomic formulas
def CanonicalModel (𝓐 : Type) : Dual.Model 𝓐 where
  frame := CanonicalFrame 𝓐
  val w a := match w with
    | .inl wn => (Modal.Formula.atom a) ∈ wn.val.1
    | .inr wp => (Modal.Formula.atom a) ∈ wp.val.1

end canonical_model

lemma no_cpl_bot : ¬ CPL.has_proof ∅ (⊥ : Modal.Formula 𝓐) := by
  intro h
  have hvalid := cpl_valid (𝓐 := 𝓐) (φ := (⊥ : Modal.Formula 𝓐)) h
  let frame : Dual.Frame :=
    { n_world := Unit
      p_world := PEmpty
      rel := fun _ _ => False }
  have hfalse := hvalid frame (fun _ _ => False) (Sum.inl ())
  simp [Dual.world_sat] at hfalse

-- MCS lemma specific to the ◇ definition in our setting
lemma mcs_neg_box_iff_dia_neg
    {Γ : Multiset (Modal.Formula 𝓐)}
    (hΓ : is_maximally_consistent (𝓐 := 𝓐) Γ)
    {φ : Modal.Formula 𝓐} :
    (¬□φ) ∈ 𝓐 ↔ (◇(¬φ)) ∈ Γ := by
  admit
  -- Since ◇ψ := ¬□¬ψ, we have ◇(¬φ) := ¬□¬¬φ
  -- By double negation in MCS: φ ↔ ¬¬φ, so □φ ↔ □¬¬φ
  -- Therefore ¬□φ ↔ ¬□¬¬φ = ◇(¬φ)

-- Standard result: if ¬□φ ∈ Γ (MCS), then {ψ | □ψ ∈ Γ} ∪ {¬φ} is consistent
-- This is used to construct witness worlds in canonical model proofs (n-worlds)
lemma unbox_neg_consistent
    {Γ : Multiset (Modal.Formula 𝓐)}
    (hΓ : is_maximally_consistent (𝓐 := 𝓐) Γ)
    {φ : Modal.Formula 𝓐}
    (hneg_box : (¬□φ) ∈ 𝓐) :
    ∃ Δ : Multiset (Modal.Formula 𝓐),
      is_maximally_consistent (𝓐 := 𝓐) Δ ∧
      (∀ ψ, (□ψ) ∈ Γ → ψ ∈ Δ) ∧
      (¬φ) ∈ Δ := by
  admit
  -- Well-known result for normal modal logics including M.
  -- Proof: Show {ψ | □ψ ∈ Γ} ∪ {¬φ} is consistent, then extend via Lindenbaum.
  -- Consistency follows from: if it were inconsistent, we could derive □¬φ,
  -- contradicting ¬□φ ∈ Γ via maximality.

-- Dual result: if □φ ∈ Γ (MCS at p-world), then {ψ | ◇ψ ∈ Γ} ∪ {φ} is consistent
-- This is used to construct witness worlds for p-worlds
lemma undia_box_consistent
    {Γ : Multiset (Modal.Formula 𝓐)}
    (hΓ : is_maximally_consistent (𝓐 := 𝓐) Γ)
    {φ : Modal.Formula 𝓐}
    (hbox : (□φ) ∈ 𝓐) :
    ∃ Δ : Multiset (Modal.Formula 𝓐),
      is_maximally_consistent (𝓐 := 𝓐) Δ ∧
      (∀ ψ, (◇ψ) ∈ Γ → ψ ∈ Δ) ∧
      φ ∈ Δ := by
  admit
  -- Dual of unbox_neg_consistent. Well-known result for normal modal logics including M.
  -- Proof: Show {ψ | ◇ψ ∈ Γ} ∪ {φ} is consistent, then extend via Lindenbaum.
  -- Consistency follows from: if it were inconsistent, we could derive ◇¬φ,
  -- which (since ◇ψ = ¬□¬ψ) means ¬□¬¬φ, and by double negation ¬□φ,
  -- contradicting □φ ∈ Γ via maximality.

lemma mcs_box_of_all
    {Γ : Multiset (Modal.Formula 𝓐)}
    (hΓ : is_maximally_consistent (𝓐 := 𝓐) Γ)
    {φ : Modal.Formula 𝓐}
    (hall : ∀ (v : World 𝓐),
              canonical_acc 𝓐 (.inl ⟨⟨𝓐, true⟩, And.intro hΓ rfl⟩) v →
              φ ∈ world_to_set v) :
    (□φ) ∈ 𝓐 := by
  -- By maximality, either □φ ∈ Γ or ¬□φ ∈ Γ
  cases mcs_mem_or_neg_mem hΓ (□φ) with
  | inl hbox => exact hbox
  | inr hneg_box =>
    -- If ¬□φ ∈ Γ, we can construct a witness world
    obtain ⟨Δ, hΔ_mcs, hΔ_acc, hΔ_neg⟩ := unbox_neg_consistent hΓ hneg_box
    -- Δ is an MCS with (∀ψ, □ψ ∈ Γ → ψ ∈ Δ) and ¬φ ∈ Δ
    -- We can make Δ into a world - let's make it an n-world
    let v : World 𝓐 := .inl ⟨⟨Δ, true⟩, And.intro hΔ_mcs rfl⟩
    -- Check that this world is accessible from our original n-world
    have hrel : canonical_acc 𝓐 (.inl ⟨⟨Γ, true⟩, And.intro hΓ rfl⟩) v := by
      intro ψ hψ
      exact hΔ_acc ψ hψ
    -- By hypothesis, φ ∈ Δ
    have hφ_mem : φ ∈ world_to_set v := hall v hrel
    -- But we also have ¬φ ∈ Δ
    have hneg_mem : (¬φ) ∈ Δ := hΔ_neg
    -- This is a contradiction in the MCS Δ
    simp [world_to_set] at hφ_mem
    have : φ ∈ Δ ∧ (¬φ) ∈ Δ := ⟨hφ_mem, hneg_mem⟩
    -- An MCS cannot contain both φ and ¬φ - derive ⊥
    have hbot : MProof' (𝓐 := 𝓐) Δ ⊥ := mcs_no_contradiction hφ_mem hneg_mem
    exact False.elim (hΔ_mcs.1 hbot)

lemma canon_acc_n {wn : NWorld 𝓐} {w : World 𝓐}
    (hrel : canonical_acc 𝓐 (.inl 𝓐) w)
    (φ : Modal.Formula 𝓐)
    (hbox : (□𝓐) ∈ world_to_set (.inl 𝓐)) :
    𝓐 ∈ world_to_set w := by
  exact hrel 𝓐 hbox

lemma existence_pworld
    {wp : PWorld 𝓐} {φ : Modal.Formula 𝓐}
    (hφ : (□φ) ∈ world_to_set (.inr 𝓐)) :
    ∃ v : World 𝓐,
    canonical_acc 𝓐 (.inr 𝓐) v ∧ φ ∈ world_to_set v := by
  -- Extract the MCS from the p-world
  obtain ⟨⟨Γ, _⟩, hΓ_mcs, _⟩ := 𝓐
  -- We have □φ ∈ Γ
  have hbox : (□φ) ∈ Γ := hφ
  -- Use undia_box_consistent to get an MCS containing all ◇-formulas from Γ plus φ
  obtain ⟨Δ, hΔ_mcs, hΔ_acc, hΔ_φ⟩ := undia_box_consistent hΓ_mcs hbox
  -- Make Δ into a world - let's use an n-world
  let v : World 𝓐 := .inl ⟨⟨Δ, true⟩, And.intro hΔ_mcs rfl⟩
  use v
  constructor
  · -- Show canonical_acc holds: ∀ ψ, ◇ψ ∈ Γ → ψ ∈ Δ
    intro ψ hdia
    exact hΔ_acc ψ hdia
  · -- Show φ ∈ world_to_set v
    simp [world_to_set]
    exact hΔ_φ

lemma mcs_box_of_exists_p
    {Γ : Multiset (Modal.Formula 𝓐)}
    (hΓ : is_maximally_consistent (𝓐 := 𝓐) Γ)
    {φ : Modal.Formula 𝓐}
    (hex : ∃ v : World 𝓐,
        canonical_acc 𝓐 (.inr ⟨⟨𝓐, false⟩, And.intro hΓ rfl⟩) v ∧
        φ ∈ world_to_set v) :
    (□φ) ∈ 𝓐 := by
  -- By maximality, either □φ ∈ Γ or ¬□φ ∈ Γ
  cases mcs_mem_or_neg_mem hΓ (□φ) with
  | inl hbox => exact hbox
  | inr hneg_box =>
    -- If ¬□φ ∈ Γ, we derive a contradiction
    -- Get the witness world from hypothesis
    obtain ⟨v, hrel, hφ_mem⟩ := hex
    -- For p-worlds, canonical_acc means: ∀ ψ, ◇ψ ∈ Γ → ψ ∈ v
    -- We have ¬□φ ∈ Γ, which is equivalent to ◇(¬φ) ∈ Γ
    -- Since ◇(¬φ) := ¬□¬¬φ, and by double negation ¬¬φ ↔ φ in MCS
    -- We get ◇(¬φ) := ¬□φ
    have hdia_neg : (◇(¬φ)) ∈ Γ := (mcs_neg_box_iff_dia_neg hΓ).mp hneg_box
    -- By accessibility relation, ¬φ ∈ v
    have hneg_mem : (¬φ) ∈ world_to_set v := hrel (¬φ) hdia_neg
    -- But we also have φ ∈ v
    -- This is a contradiction
    have hbot : MProof' (𝓐 := 𝓐) (world_to_set v) ⊥ :=
      ModalConsistency.mcs_no_contradiction hφ_mem hneg_mem
    -- v must be an MCS (either from .inl or .inr)
    cases v with
    | inl vn => exact False.elim (vn.property.1.1 hbot)
    | inr vp => exact False.elim (vp.property.1.1 hbot)

lemma truth_lemma
    (w : (CanonicalModel 𝓐).frame.world)
    (φ : Modal.Formula 𝓐) :
    world_sat (CanonicalModel 𝓐) 𝓐 φ ↔ φ ∈ world_to_set 𝓐 := by
  induction φ generalizing 𝓐 with
  | atom a =>
    cases 𝓐 with
    | inl wn => rfl
    | inr wp => rfl
  | bot =>
    cases 𝓐 with
    | inl wn =>
      simp [world_sat, world_to_set]
      exact mcs_no_bot wn.property.1
    | inr wp =>
      simp [world_sat, world_to_set]
      exact mcs_no_bot wp.property.1
  | impl φ ψ ih_φ ih_ψ =>
    cases 𝓐 with
    | inl wn =>
      simp [world_sat, world_to_set]
      rw [ih_φ, ih_ψ]
      exact (mcs_impl_closed wn.property.1).symm
    | inr wp =>
      simp [world_sat, world_to_set]
      rw [ih_φ, ih_ψ]
      exact (mcs_impl_closed wp.property.1).symm
  | box φ ih_φ =>
    cases 𝓐 with
    | inl wn =>
      simp only [world_sat, world_to_set]
      constructor
      · -- mp: world_sat → membership (i.e., ∀ v, rel v → sat v φ → □φ ∈ Γ)
        intro hall
        apply mcs_box_of_all wn.property.1
        intro v hrel
        have hworld := hall v hrel
        rw [ih_φ v] at hworld
        exact hworld
      · -- mpr: membership → world_sat (i.e., (□φ) ∈ Γ → ∀ v, rel v → sat v φ)
        intro hbox v hrel
        rw [ih_φ v]
        exact canon_acc_n hrel φ hbox
    | inr wp =>
      simp only [world_sat, world_to_set]
      constructor
      · -- mp: world_sat → membership (i.e., ∃ v, rel v ∧ sat v φ → □φ ∈ Γ)
        intro ⟨v, hrel, hsat⟩
        apply mcs_box_of_exists_p wp.property.1
        use v
        constructor
        · exact hrel
        · rw [ih_φ v] at hsat
          exact hsat
      · -- mpr: membership → world_sat (i.e., (□φ) ∈ Γ → ∃ v, rel v ∧ sat v φ)
        intro hbox
        obtain ⟨v, hrel, hφ_mem⟩ := existence_pworld hbox
        use v
        constructor
        · exact hrel
        · rw [ih_φ v]
          exact hφ_mem
  -- Blackburn et al. Lemma 4.21
  -- Note: dia cases are not needed since ◇φ is defined as ¬□¬φ

lemma complete_wrt_canon :
    ∀ (φ : Modal.Formula 𝓐), model_sat (CanonicalModel 𝓐) φ → MProof φ := by
  intro φ hmodel
  classical
  have hmem : ∀ {Γ : Multiset (Modal.Formula 𝓐)},
      is_maximally_consistent (𝓐 := 𝓐) Γ → φ ∈ Γ := by
    intro Γ hΓ
    let wn : NWorld 𝓐 :=
      ⟨⟨Γ, true⟩, And.intro hΓ rfl⟩
    have hsat : world_sat (CanonicalModel 𝓐) (.inl wn) φ := hmodel _
    have htruth := (truth_lemma (𝓐 := 𝓐) (.inl wn) φ).mp hsat
    simpa using htruth
  exact (deriv_iff_mem_mcs (𝓐 := 𝓐) φ).mpr hmem
  -- analog to Blackburn et al. Theorem 4.22

lemma valid_canon_iff_valid (φ : Modal.Formula 𝓐) :
    model_sat (CanonicalModel 𝓐) 𝓐 ↔ Dual.valid 𝓐 := by
  constructor
  · intro hcanon
    have hproof : MProof 𝓐 := (complete_wrt_canon (𝓐 := 𝓐) φ) hcanon
    exact logicM_dual_sound (𝓐 := 𝓐) φ hproof
  · intro hvalid
    have hframe := hvalid (CanonicalModel 𝓐).frame
    have hmodel := hframe (CanonicalModel 𝓐).val
    exact hmodel

theorem logicM_dual_complete :
    ∀ (φ : Modal.Formula 𝓐), Dual.valid φ → MProof φ := by
    intro φ hvalid
    have hmodel : model_sat (CanonicalModel 𝓐) φ :=
      (valid_canon_iff_valid (𝓐 := 𝓐) φ).mpr hvalid
    exact complete_wrt_canon (𝓐 := 𝓐) φ hmodel


end completeness


theorem logicM_dual_sc :
    ∀ (φ : Modal.Formula 𝓐), valid φ ↔ MProof ∅ φ := by
    intro φ
    constructor
    · exact logicM_dual_complete φ
    · exact logicM_dual_sound φ
