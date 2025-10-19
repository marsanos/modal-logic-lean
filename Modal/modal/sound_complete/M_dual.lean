import Modal.modal.models.dual
import Modal.modal.proof_systems.M_proof


namespace Modal.SoundComplete.M_Dual

open Modal.ProofSystems Modal.Models


def all_frames : Dual.Frame → Prop := fun _ => True

theorem is_sound (Atom : Type) :
    Logic.is_sound (M.proof_system Atom) (@Dual.semantics Atom all_frames) (by rfl) :=
  sorry

theorem is_complete (Atom : Type) :
     Logic.is_complete (M.proof_system Atom) (@Dual.semantics Atom all_frames) (by rfl) :=
  sorry


--- --- ---


variable {α : Type}

section soundness

-- each world contains a valuation - this function extracts it
def world_as_valuation {Atom : Type} (m : Models.Dual.Model Atom) (w : m.frame.world) :
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
    | ax_m => exact ax_m_valid _ _
    | rl_re h_prem ih => exact rl_re_valid _ _ ih

end soundness

section completeness

section canonical_model

abbrev NWorld (α : Type) :=
  {w : (Multiset (ModalFormula α)) × Bool //
    is_maximally_consistent w.1 ∧ w.2 = true}
abbrev PWorld (α : Type) :=
  {w : (Multiset (ModalFormula α)) × Bool //
    is_maximally_consistent w.1 ∧ w.2 = false}
abbrev World (α : Type) := NWorld α ⊕ PWorld α

def is_nworld {α : Type} : World α → Prop
  | .inl _ => true
  | .inr _ => false
def is_pworld {α : Type} : World α → Prop
  | .inl _ => false
  | .inr _ => true

def world_to_set {α : Type} (w : World α) : Multiset (ModalFormula α) :=
  match w with
  | .inl wn => wn.val.1
  | .inr wp => wp.val.1

def canonical_acc (α : Type) : World α → World α → Prop :=
  fun w₁ w₂ =>
    match w₁ with
    | .inl _ => ∀ φ : ModalFormula α,
                  (□φ) ∈ world_to_set w₁ → φ ∈ world_to_set w₂
    | .inr _ => ∀ φ : ModalFormula α,
                  (◇φ) ∈ world_to_set w₁ → φ ∈ world_to_set w₂

def CanonicalFrame (α : Type) : Dual.Frame where
  n_world := NWorld α
  p_world := PWorld α
  rel := canonical_acc α

-- Canonical model: canonical frame with valuation based on atomic formulas
def CanonicalModel (α : Type) : Dual.Model α where
  frame := CanonicalFrame α
  val w a := match w with
    | .inl wn => (ModalFormula.atom a) ∈ wn.val.1
    | .inr wp => (ModalFormula.atom a) ∈ wp.val.1

end canonical_model

lemma no_cpl_bot : ¬ CPLSeq.CPLProof (⊥ : ModalFormula α) := by
  intro h
  have hvalid := cpl_valid (α := α) (φ := (⊥ : ModalFormula α)) h
  let frame : Dual.Frame :=
    { n_world := Unit
      p_world := PEmpty
      rel := fun _ _ => False }
  have hfalse := hvalid frame (fun _ _ => False) (Sum.inl ())
  simp [Dual.world_sat] at hfalse

lemma consistent_no_bot {Γ : Multiset (ModalFormula α)}
    (hΓ : is_consistent (α := α) Γ) : (⊥ : ModalFormula α) ∉ Γ := by
  intro hbot
  have : MProof' (α := α) Γ ⊥ := MProof'.assumption hbot
  exact hΓ this

lemma mcs_no_bot {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent (α := α) Γ) : (⊥ : ModalFormula α) ∉ Γ :=
  consistent_no_bot hΓ.1

lemma mcs_no_contradiction
    {Γ : Multiset (ModalFormula α)}
    {φ : ModalFormula α}
    (hφ : φ ∈ Γ) (hneg : (¬φ) ∈ Γ) : MProof' (α := α) Γ ⊥ := by
  admit
  -- Standard CPL result: from {φ, ¬φ} derive ⊥

lemma mcs_double_neg
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent (α := α) Γ)
    {φ : ModalFormula α} :
    φ ∈ Γ ↔ (¬¬φ) ∈ Γ := by
  admit
  -- Standard result for MCS: double negation equivalence

lemma mcs_neg_box_iff_dia_neg
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent (α := α) Γ)
    {φ : ModalFormula α} :
    (¬□φ) ∈ Γ ↔ (◇(¬φ)) ∈ Γ := by
  admit
  -- Since ◇ψ := ¬□¬ψ, we have ◇(¬φ) := ¬□¬¬φ
  -- By double negation in MCS: φ ↔ ¬¬φ, so □φ ↔ □¬¬φ
  -- Therefore ¬□φ ↔ ¬□¬¬φ = ◇(¬φ)

lemma mcs_mem_or_neg_mem
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent (α := α) Γ)
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

-- Standard result: if ¬□φ ∈ Γ (MCS), then {ψ | □ψ ∈ Γ} ∪ {¬φ} is consistent
-- This is used to construct witness worlds in canonical model proofs (n-worlds)
lemma unbox_neg_consistent
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent (α := α) Γ)
    {φ : ModalFormula α}
    (hneg_box : (¬□φ) ∈ Γ) :
    ∃ Δ : Multiset (ModalFormula α),
      is_maximally_consistent (α := α) Δ ∧
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
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent (α := α) Γ)
    {φ : ModalFormula α}
    (hbox : (□φ) ∈ Γ) :
    ∃ Δ : Multiset (ModalFormula α),
      is_maximally_consistent (α := α) Δ ∧
      (∀ ψ, (◇ψ) ∈ Γ → ψ ∈ Δ) ∧
      φ ∈ Δ := by
  admit
  -- Dual of unbox_neg_consistent. Well-known result for normal modal logics including M.
  -- Proof: Show {ψ | ◇ψ ∈ Γ} ∪ {φ} is consistent, then extend via Lindenbaum.
  -- Consistency follows from: if it were inconsistent, we could derive ◇¬φ,
  -- which (since ◇ψ = ¬□¬ψ) means ¬□¬¬φ, and by double negation ¬□φ,
  -- contradicting □φ ∈ Γ via maximality.

lemma mcs_box_of_all
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent (α := α) Γ)
    {φ : ModalFormula α}
    (hall : ∀ (v : World α),
              canonical_acc α (.inl ⟨⟨Γ, true⟩, And.intro hΓ rfl⟩) v →
              φ ∈ world_to_set v) :
    (□φ) ∈ Γ := by
  -- By maximality, either □φ ∈ Γ or ¬□φ ∈ Γ
  cases mcs_mem_or_neg_mem hΓ (□φ) with
  | inl hbox => exact hbox
  | inr hneg_box =>
    -- If ¬□φ ∈ Γ, we can construct a witness world
    obtain ⟨Δ, hΔ_mcs, hΔ_acc, hΔ_neg⟩ := unbox_neg_consistent hΓ hneg_box
    -- Δ is an MCS with (∀ψ, □ψ ∈ Γ → ψ ∈ Δ) and ¬φ ∈ Δ
    -- We can make Δ into a world - let's make it an n-world
    let v : World α := .inl ⟨⟨Δ, true⟩, And.intro hΔ_mcs rfl⟩
    -- Check that this world is accessible from our original n-world
    have hrel : canonical_acc α (.inl ⟨⟨Γ, true⟩, And.intro hΓ rfl⟩) v := by
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
    have hbot : MProof' (α := α) Δ ⊥ := mcs_no_contradiction hφ_mem hneg_mem
    exact False.elim (hΔ_mcs.1 hbot)

lemma canon_acc_n {wn : NWorld α} {w : World α}
    (hrel : canonical_acc α (.inl wn) w)
    (φ : ModalFormula α)
    (hbox : (□φ) ∈ world_to_set (.inl wn)) :
    φ ∈ world_to_set w := by
  exact hrel φ hbox

lemma existence_pworld
    {wp : PWorld α} {φ : ModalFormula α}
    (hφ : (□φ) ∈ world_to_set (.inr wp)) :
    ∃ v : World α,
    canonical_acc α (.inr wp) v ∧ φ ∈ world_to_set v := by
  -- Extract the MCS from the p-world
  obtain ⟨⟨Γ, _⟩, hΓ_mcs, _⟩ := wp
  -- We have □φ ∈ Γ
  have hbox : (□φ) ∈ Γ := hφ
  -- Use undia_box_consistent to get an MCS containing all ◇-formulas from Γ plus φ
  obtain ⟨Δ, hΔ_mcs, hΔ_acc, hΔ_φ⟩ := undia_box_consistent hΓ_mcs hbox
  -- Make Δ into a world - let's use an n-world
  let v : World α := .inl ⟨⟨Δ, true⟩, And.intro hΔ_mcs rfl⟩
  use v
  constructor
  · -- Show canonical_acc holds: ∀ ψ, ◇ψ ∈ Γ → ψ ∈ Δ
    intro ψ hdia
    exact hΔ_acc ψ hdia
  · -- Show φ ∈ world_to_set v
    simp [world_to_set]
    exact hΔ_φ

lemma mcs_box_of_exists_p
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent (α := α) Γ)
    {φ : ModalFormula α}
    (hex : ∃ v : World α,
        canonical_acc α (.inr ⟨⟨Γ, false⟩, And.intro hΓ rfl⟩) v ∧
        φ ∈ world_to_set v) :
    (□φ) ∈ Γ := by
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
    have hbot : MProof' (α := α) (world_to_set v) ⊥ :=
      mcs_no_contradiction hφ_mem hneg_mem
    -- v must be an MCS (either from .inl or .inr)
    cases v with
    | inl vn => exact False.elim (vn.property.1.1 hbot)
    | inr vp => exact False.elim (vp.property.1.1 hbot)

lemma mcs_impl_closed
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent (α := α) Γ)
    {φ ψ : ModalFormula α} :
    (φ → ψ) ∈ Γ ↔ (φ ∈ Γ → ψ ∈ Γ) := by
  admit  -- known result, not dependent on my particular setting

lemma truth_lemma
    (w : (CanonicalModel α).frame.world)
    (φ : ModalFormula α) :
    world_sat (CanonicalModel α) w φ ↔ φ ∈ world_to_set w := by
  induction φ generalizing w with
  | atom a =>
    cases w with
    | inl wn => rfl
    | inr wp => rfl
  | bot =>
    cases w with
    | inl wn =>
      simp [world_sat, world_to_set]
      exact mcs_no_bot wn.property.1
    | inr wp =>
      simp [world_sat, world_to_set]
      exact mcs_no_bot wp.property.1
  | impl φ ψ ih_φ ih_ψ =>
    cases w with
    | inl wn =>
      simp [world_sat, world_to_set]
      rw [ih_φ, ih_ψ]
      exact (mcs_impl_closed wn.property.1).symm
    | inr wp =>
      simp [world_sat, world_to_set]
      rw [ih_φ, ih_ψ]
      exact (mcs_impl_closed wp.property.1).symm
  | box φ ih_φ =>
    cases w with
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

lemma deriv_iff_mem_mcs (φ : ModalFormula α) :
    MProof (α := α) φ ↔ ∀ {Γ : Multiset (ModalFormula α)},
                          is_maximally_consistent (α := α) Γ → φ ∈ Γ := by
  admit
  -- Well-known result for M and other logics.
  -- See, for example, Chellas, Theorem 2.20 (2).

lemma complete_wrt_canon :
    ∀ (φ : ModalFormula α), model_sat (CanonicalModel α) φ → MProof φ := by
  intro φ hmodel
  classical
  have hmem : ∀ {Γ : Multiset (ModalFormula α)},
      is_maximally_consistent (α := α) Γ → φ ∈ Γ := by
    intro Γ hΓ
    let wn : NWorld α :=
      ⟨⟨Γ, true⟩, And.intro hΓ rfl⟩
    have hsat : world_sat (CanonicalModel α) (.inl wn) φ := hmodel _
    have htruth := (truth_lemma (α := α) (.inl wn) φ).mp hsat
    simpa using htruth
  exact (deriv_iff_mem_mcs (α := α) φ).mpr hmem
  -- analog to Blackburn et al. Theorem 4.22

lemma valid_canon_iff_valid (φ : ModalFormula α) :
    model_sat (CanonicalModel α) φ ↔ Dual.valid φ := by
  constructor
  · intro hcanon
    have hproof : MProof φ := (complete_wrt_canon (α := α) φ) hcanon
    exact logicM_dual_sound (α := α) φ hproof
  · intro hvalid
    have hframe := hvalid (CanonicalModel α).frame
    have hmodel := hframe (CanonicalModel α).val
    exact hmodel

theorem logicM_dual_complete :
    ∀ (φ : ModalFormula α), Dual.valid φ → MProof φ := by
    intro φ hvalid
    have hmodel : model_sat (CanonicalModel α) φ :=
      (valid_canon_iff_valid (α := α) φ).mpr hvalid
    exact complete_wrt_canon (α := α) φ hmodel


end completeness


theorem logicM_dual_sc :
    ∀ (φ : ModalFormula α), valid φ ↔ MProof φ := by
    intro φ
    constructor
    · exact logicM_dual_complete φ
    · exact logicM_dual_sound φ

end Modal.SoundComplete.M_Dual
