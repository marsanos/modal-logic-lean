import Modal.modal.formula
import Modal.modal.models.dual
import Modal.modal.axioms_rules
import Modal.modal.consistency
import Modal.cpl.metatheorems
import Modal.cpl.theorems


open ModalFormula Dual ModalAxioms ModalRules ModalConsistency CPLTheorems

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

lemma mcs_box_of_all
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent (α := α) Γ)
    {φ : ModalFormula α}
    (hall : ∀ (v : World α),
              canonical_acc α (.inl ⟨⟨Γ, true⟩, And.intro hΓ rfl⟩) v →
              φ ∈ world_to_set v) :
    (□φ) ∈ Γ := by
  sorry

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
  sorry
  -- Blackburn et al. Proposition 4.20

lemma mcs_box_of_exists_p
    {Γ : Multiset (ModalFormula α)}
    (hΓ : is_maximally_consistent (α := α) Γ)
    {φ : ModalFormula α}
    (hex : ∃ v : World α,
        canonical_acc α (.inr ⟨⟨Γ, false⟩, And.intro hΓ rfl⟩) v ∧
        φ ∈ world_to_set v) :
    (□φ) ∈ Γ := by
  sorry

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
  | dia φ ih_φ =>
    cases w with
    | inl wn =>
      sorry
    | inr wp =>
      sorry
  -- Blackburn et al. Lemma 4.21

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
