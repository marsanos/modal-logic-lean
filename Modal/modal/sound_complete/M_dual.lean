import Modal.modal.models.dual
import Modal.modal.proof_systems.M_proof
import Modal.cpl.proof


namespace Modal.SoundComplete.M_Dual

open Modal.ProofSystems Modal.Models


def all_frames : Dual.Frame → Prop := fun _ => True


section soundness

-- each world contains a valuation - this function extracts it
def world_as_valuation {Atom : Type} (m : Dual.Model Atom all_frames) (w : m.frame.world) :
    CPL.Valuation (Modal.Formula Atom) where
  val := Dual.world_sat m w
  h_val_bot := rfl
  h_val_impl _ _ := rfl

-- So that the proof is not too long, we prove some helper lemmas first.

-- Helper function to evaluate CPL formulas where atoms are modal formulas
def eval_cpl_with_modal_atoms {Atom : Type} (m : Dual.Model Atom all_frames) (w : m.frame.world) :
    CPL.Formula (Modal.Formula Atom) → Prop
  | CPL.Formula.atom modal_f => Dual.world_sat m w modal_f
  | CPL.Formula.bot => False
  | CPL.Formula.impl ψ1 ψ2 => (eval_cpl_with_modal_atoms m w ψ1 → eval_cpl_with_modal_atoms m w ψ2)

-- The CPL translation preserves semantics
lemma to_cpl_preserves_sat {Atom : Type} (m : Dual.Model Atom all_frames)
    (w : m.frame.world) (φ : Modal.Formula Atom) :
    eval_cpl_with_modal_atoms m w (to_cpl φ) ↔ Dual.world_sat m w φ := by
  induction φ with
  | atom a =>
    -- to_cpl (atom a) = CPL.atom (Modal.atom a)
    simp [to_cpl, eval_cpl_with_modal_atoms]
  | bot =>
    -- to_cpl bot = CPL.bot
    simp [to_cpl, eval_cpl_with_modal_atoms, Dual.world_sat]
  | impl φ₁ φ₂ ih₁ ih₂ =>
    -- to_cpl (φ₁ → φ₂) = CPL.impl (to_cpl φ₁) (to_cpl φ₂)
    simp [to_cpl, eval_cpl_with_modal_atoms, Dual.world_sat]
    constructor
    · intro h hsat₁
      apply ih₂.mp
      apply h
      exact ih₁.mpr hsat₁
    · intro h heval₁
      apply ih₂.mpr
      apply h
      exact ih₁.mp heval₁
  | box φ ih =>
    -- to_cpl (□φ) = CPL.atom (Modal.box φ)
    simp [to_cpl, eval_cpl_with_modal_atoms]

-- CPL tautologies are valid in dual models
lemma cpl_is_valid {Atom : Type} (φ : Modal.Formula Atom)
    (h : (CPL.proof_system (Modal.Formula Atom)).entails ∅ (to_cpl φ)) :
    Dual.is_valid (fun _ => True) φ := by
  intro m w
  -- Create a CPL valuation for CPL formulas where atoms are modal formulas
  let v : CPL.Valuation (CPL.Formula (Modal.Formula Atom)) := {
    val := eval_cpl_with_modal_atoms m w
    h_val_bot := rfl
    h_val_impl := fun _ _ => rfl
  }
  have sound := CPL.is_sound (Modal.Formula Atom)
  -- Apply soundness to get semantic consequence
  have sem := sound ∅ (to_cpl φ) h
  -- Unfold the definitions to see the structure
  unfold Logic.is_sem_conseq at sem
  -- Simplify with the fact that CPL.semantics has model = Valuation and satisfies = val
  simp [CPL.semantics] at sem
  -- Now sem : ∀ (M : CPL.Valuation (CPL.Formula (Formula Atom))), M.val (to_cpl φ)
  have sat := sem v
  -- sat : v.val (to_cpl φ), which is eval_cpl_with_modal_atoms m w (to_cpl φ)
  -- Use the preservation lemma to relate CPL satisfaction to Modal satisfaction
  exact (to_cpl_preserves_sat m w φ).mp sat

lemma ax_m_is_valid {Atom : Type} (φ ψ : Modal.Formula Atom) :
    Dual.is_valid (fun _ => True) (Axioms.m φ ψ) := by
  intro m w
  unfold Axioms.m
  -- Goal: world_sat m w (□(φ ∧ ψ) → □φ)
  simp [Dual.world_sat]
  cases w with
  | inl wn =>
    -- At n-world: □(φ∧ψ) → □φ
    intro h v hrel
    have hpq := h v hrel
    -- hpq : world_sat m v (φ ∧ ψ)
    -- ∧ is defined as ¬(φ → ¬ψ)
    unfold CPL.Syntax.and CPL.Syntax.neg at hpq
    simp [Dual.world_sat] at hpq
    -- hpq should now be: ¬((world_sat m v φ → False) → False)
    -- which simplifies to: world_sat m v φ ∧ world_sat m v ψ
    exact hpq.1
  | inr wp =>
    -- At p-world: □(φ∧ψ) → □φ
    intro ⟨v, hrel, hpq⟩
    unfold CPL.Syntax.and CPL.Syntax.neg at hpq
    simp [Dual.world_sat] at hpq
    exact ⟨v, hrel, hpq.1⟩

-- Helper lemma that works with the induction hypothesis structure from is_sound
lemma rl_re_is_valid {Atom : Type} {Γ : Set (Modal.Formula Atom)} (φ ψ : Modal.Formula Atom)
    (ih : ∀ (model : Dual.Model Atom all_frames)
            (_hΓ : ∀ ψ_Γ ∈ Set.image id Γ, Dual.model_sat model ψ_Γ),
          Dual.model_sat model (φ ↔ ψ)) :
    ∀ (model : Dual.Model Atom all_frames)
      (_hΓ : ∀ ψ_Γ ∈ Set.image id Γ, Dual.model_sat model ψ_Γ),
      Dual.model_sat model (□φ ↔ □ψ) := by
  intro model hΓ w
  simp only [CPL.Syntax.iff, CPL.Syntax.and, CPL.Syntax.neg, Dual.world_sat]
  cases w with
  | inl wn =>
    intro h_contra
    apply h_contra
    · -- Prove □φ → □ψ
      intro h_box_phi v hrel
      have hv := ih model hΓ v
      have hphi := h_box_phi v hrel
      by_contra h_not_psi
      apply hv
      intro h_fwd h_bwd
      unfold Dual.world_sat at h_fwd
      exact h_not_psi (h_fwd hphi)
    · -- Prove □ψ → □φ
      intro h_box_psi v hrel
      have hv := ih model hΓ v
      have hpsi := h_box_psi v hrel
      by_contra h_not_phi
      apply hv
      intro h_fwd h_bwd
      unfold Dual.world_sat at h_bwd
      exact h_not_phi (h_bwd hpsi)
  | inr wp =>
    intro h_contra
    apply h_contra
    · -- Prove □φ → □ψ
      intro ⟨v, hrel, hphi⟩
      have hv := ih model hΓ v
      use v, hrel
      by_contra h_not_psi
      apply hv
      intro h_fwd h_bwd
      unfold Dual.world_sat at h_fwd
      exact h_not_psi (h_fwd hphi)
    · -- Prove □ψ → □φ
      intro ⟨v, hrel, hpsi⟩
      have hv := ih model hΓ v
      use v, hrel
      by_contra h_not_phi
      apply hv
      intro h_fwd h_bwd
      unfold Dual.world_sat at h_bwd
      exact h_not_phi (h_bwd hpsi)

theorem is_sound {Atom : Type} :
    Logic.is_sound (M.proof_system Atom) (@Dual.semantics Atom all_frames) (by rfl) := by
  intro Γ φ
  -- Unfold the definition to see what we need to prove
  change M.proof Γ φ → Logic.is_sem_conseq (@Dual.semantics Atom all_frames)
                                           (Set.image id Γ) φ
  intro hproof model hΓ
  -- model : Dual.Model Atom all_frames
  -- hΓ : ∀ ψ ∈ Set.image id Γ, Dual.model_sat model ψ
  -- Goal: Dual.model_sat model φ
  induction hproof generalizing model with
  | assumption hmem => exact hΓ _ (Set.mem_image_of_mem id hmem)
  | cpl h_cpl => exact cpl_is_valid _ h_cpl model
  | m => exact ax_m_is_valid _ _ model
  | re h_prem ih_prem => exact rl_re_is_valid _ _ ih_prem model hΓ

end soundness


section completeness

section canonical_model
/-
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
-/
end canonical_model
/-
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

-/

theorem is_complete (Atom : Type) :
     Logic.is_complete (M.proof_system Atom) (@Dual.semantics Atom all_frames) (by rfl) :=
  sorry

end completeness

/-
theorem logicM_dual_sc :
    ∀ (φ : ModalFormula α), valid φ ↔ MProof φ := by
    intro φ
    constructor
    · exact logicM_dual_complete φ
    · exact logicM_dual_sound φ

end Modal.SoundComplete.M_Dual
-/

end Modal.SoundComplete.M_Dual
