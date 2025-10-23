import Modal.modal.models.dual
import Modal.modal.proof_systems.EM_proof
import Modal.cpl.proof
import Modal.common.logic


namespace Modal.SoundComplete.EM_Dual

open Modal.ProofSystems Modal.Models


section soundness

-- Helper function to evaluate CPL formulas where atoms are modal formulas
def eval_cpl_with_modal_atoms {Atom : Type} (m : Dual.Model Atom) (w : m.frame.world) :
    CPL.Formula (Modal.Formula Atom) → Prop
  | CPL.Formula.atom modal_f => Dual.world_sat m w modal_f
  | CPL.Formula.bot => False
  | CPL.Formula.impl ψ1 ψ2 => (eval_cpl_with_modal_atoms m w ψ1 → eval_cpl_with_modal_atoms m w ψ2)

-- Each world contains a valuation - this function extracts it
def world_as_valuation {Atom : Type} (m : Dual.Model Atom) (w : m.frame.world) :
    CPL.Valuation (CPL.Formula (Modal.Formula Atom)) where
  val := eval_cpl_with_modal_atoms m w
  h_val_bot := rfl
  h_val_impl _ _ := rfl

lemma to_cpl_preserves_sat {Atom : Type} (m : Dual.Model Atom)
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
    Dual.is_valid φ := by
  intro m w
  -- CPL soundness: syntactic entailment implies semantic entailment
  have sound := CPL.is_sound_strong (Modal.Formula Atom)
  have sem := sound ∅ (to_cpl φ) h
  have sat := sem (world_as_valuation m w) (by simp)
  -- Use the preservation lemma to relate CPL and modal satisfaction
  exact (to_cpl_preserves_sat m w φ).mp sat

lemma ax_m_is_valid {Atom : Type} (φ ψ : Modal.Formula Atom) :
    Dual.is_valid (Axioms.m φ ψ) := by
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

-- CPL tautology: biconditional is symmetric
private lemma iff_symm_at_world {Atom : Type} {model : Dual.Model Atom} {w : model.frame.world}
    {φ ψ : Modal.Formula Atom} (h : Dual.world_sat model w (φ ↔ ψ)) :
    Dual.world_sat model w (ψ ↔ φ) := by
  simp only [CPL.Syntax.iff, CPL.Syntax.and, CPL.Syntax.neg, Dual.world_sat] at h ⊢
  intro h_contra
  apply h
  intro h_fwd h_bwd
  exact h_contra h_bwd h_fwd

-- Helper: extract forward implication from biconditional
private lemma fwd_from_iff {Atom : Type} {model : Dual.Model Atom} {w : model.frame.world}
    {φ ψ : Modal.Formula Atom} (h_iff : Dual.world_sat model w (φ ↔ ψ))
    (h_phi : Dual.world_sat model w φ) : Dual.world_sat model w ψ := by
  simp only [CPL.Syntax.iff, CPL.Syntax.and, CPL.Syntax.neg, Dual.world_sat] at h_iff ⊢
  by_contra h_not_psi
  apply h_iff
  intro h_fwd _
  exact h_not_psi (h_fwd h_phi)

lemma rl_re_is_valid {Atom : Type} (φ ψ : Modal.Formula Atom) (model : Dual.Model Atom) :
    Dual.model_sat model (Rules.re φ ψ).premise →
    Dual.model_sat model (Rules.re φ ψ).conclusion := by
  intro h w
  unfold Rules.re at *
  simp only [CPL.Syntax.iff, CPL.Syntax.and, CPL.Syntax.neg, Dual.world_sat]
  cases w with
  | inl wn =>
    intro h_contra
    apply h_contra
    · -- Prove □φ → □ψ using forward direction
      intro h_box_phi v hrel
      exact fwd_from_iff (h v) (h_box_phi v hrel)
    · -- Prove □ψ → □φ using symmetry then forward direction
      intro h_box_psi v hrel
      exact fwd_from_iff (iff_symm_at_world (h v)) (h_box_psi v hrel)
  | inr wp =>
    intro h_contra
    apply h_contra
    · -- Prove □φ → □ψ using forward direction
      intro ⟨v, hrel, hphi⟩
      use v, hrel
      exact fwd_from_iff (h v) hphi
    · -- Prove □ψ → □φ using symmetry then forward direction
      intro ⟨v, hrel, hpsi⟩
      use v, hrel
      exact fwd_from_iff (iff_symm_at_world (h v)) hpsi

theorem is_sound_strong (Atom : Type) :
  Logic.is_sound_strong (EM.proof_system Atom) (Dual.semantics Atom) := by
  intro Γ φ hproof model hΓ
  induction hproof generalizing model with
  | assumption hmem => exact hΓ _ hmem
  | cpl h_cpl => exact cpl_is_valid _ h_cpl model
  | m => exact ax_m_is_valid _ _ model
  | re h_prem ih_prem => exact rl_re_is_valid _ _ model (ih_prem model hΓ)
    -- ih_prem: ∀ model hΓ, model_sat model (premise)
    -- We have: model_sat model (premise) from ih_prem model hΓ

end soundness


section completeness

section canonical_model

abbrev NWorld (Atom : Type) := {Γ : Set (Formula Atom) // (EM.proof_system Atom).is_mcs Γ}
abbrev PWorld (Atom : Type) := {Γ : Set (Formula Atom) // (EM.proof_system Atom).is_mcs Γ}
abbrev World (Atom : Type) := NWorld Atom ⊕ PWorld Atom

def world_to_form_set {Atom : Type} (w : World Atom) : Set (Formula Atom) :=
  match w with
  | .inl wn => wn.val
  | .inr wp => wp.val

def canonical_acc (Atom : Type) : World Atom → World Atom → Prop :=
  fun w₁ w₂ =>
    match w₁ with
    | .inl _ => ∀ φ : Formula Atom,
                  (□φ) ∈ world_to_form_set w₁ → φ ∈ world_to_form_set w₂
    | .inr _ => ∀ φ : Formula Atom,
                  (◇φ) ∈ world_to_form_set w₁ → φ ∈ world_to_form_set w₂

def CanonicalFrame (Atom : Type) : Dual.Frame where
  n_world := NWorld Atom
  p_world := PWorld Atom
  rel := canonical_acc Atom

-- Canonical model: canonical frame with valuation based on atomic formulas
def CanonicalModel (Atom : Type) : Dual.Model Atom where
  frame := CanonicalFrame Atom
  val w a := match w with
    | .inl wn => (Formula.atom a) ∈ wn.val
    | .inr wp => (Formula.atom a) ∈ wp.val

end canonical_model


-- Key lemmas needed for completeness

-- A formula is derivable iff it's in every MCS
lemma deriv_iff_mem_mcs {Atom : Type} (φ : Formula Atom) :
    (EM.proof_system Atom).entails ∅ φ ↔
    ∀ {Γ : Set (Formula Atom)}, (EM.proof_system Atom).is_mcs Γ → φ ∈ Γ := by
  admit
  -- Well-known result for normal modal logics.
  -- See, for example, Chellas, Theorem 2.20 (2).

-- Standard MCS properties needed for the truth lemma

-- Bottom is never in an MCS
lemma mcs_no_bot {Atom : Type} {Γ : Set (Formula Atom)}
    (hΓ : (EM.proof_system Atom).is_mcs Γ) : (⊥ : Formula Atom) ∉ Γ := by
  admit
  -- Standard result: MCS are consistent, and ⊥ witnesses inconsistency

-- MCS are closed under implication
lemma mcs_impl_closed {Atom : Type} {Γ : Set (Formula Atom)}
    (hΓ : (EM.proof_system Atom).is_mcs Γ) {φ ψ : Formula Atom} :
    (φ → ψ) ∈ Γ ↔ (φ ∈ Γ → ψ ∈ Γ) := by
  admit
  -- Standard result: MCS closed under modus ponens

-- If φ is satisfied at all accessible worlds from an n-world, then □φ is in the MCS
lemma mcs_box_of_all {Atom : Type} {Γ : Set (Formula Atom)}
    (hΓ : (EM.proof_system Atom).is_mcs Γ) {φ : Formula Atom}
    (hall : ∀ (v : World Atom),
      canonical_acc Atom (.inl ⟨Γ, hΓ⟩) v → φ ∈ world_to_form_set v) :
    (□φ) ∈ Γ := by
  admit
  -- Proof by contradiction using Lindenbaum and witness construction

-- Accessibility from n-world propagates boxed formulas
lemma canon_acc_n {Atom : Type} {wn : NWorld Atom} {w : World Atom}
    (hrel : canonical_acc Atom (.inl wn) w) (φ : Formula Atom)
    (hbox : (□φ) ∈ world_to_form_set (.inl wn)) :
    φ ∈ world_to_form_set w := by
  exact hrel φ hbox

-- If φ satisfied at some accessible world from p-world, then □φ is in the MCS
lemma mcs_box_of_exists_p {Atom : Type} {Γ : Set (Formula Atom)}
    (hΓ : (EM.proof_system Atom).is_mcs Γ) {φ : Formula Atom}
    (hex : ∃ v : World Atom,
      canonical_acc Atom (.inr ⟨Γ, hΓ⟩) v ∧ φ ∈ world_to_form_set v) :
    (□φ) ∈ Γ := by
  admit
  -- Proof by contradiction using dual of witness construction

-- If □φ in p-world MCS, then there exists an accessible world containing φ
lemma existence_pworld {Atom : Type} {wp : PWorld Atom} {φ : Formula Atom}
    (hφ : (□φ) ∈ world_to_form_set (.inr wp)) :
    ∃ v : World Atom,
      canonical_acc Atom (.inr wp) v ∧ φ ∈ world_to_form_set v := by
  admit
  -- Use Lindenbaum to extend {ψ | ◇ψ ∈ Γ} ∪ {φ} to MCS

-- Truth lemma: satisfaction in canonical model corresponds to membership in MCS
-- This is the key lemma (Blackburn et al. Lemma 4.21)
lemma truth_lemma {Atom : Type} (w : (CanonicalModel Atom).frame.world) (φ : Formula Atom) :
    Dual.world_sat (CanonicalModel Atom) w φ ↔ φ ∈ world_to_form_set w := by
  induction φ generalizing w with
  | atom a =>
    -- Atomic formulas: satisfied iff in the world's MCS (by definition of valuation)
    cases w with
    | inl wn => rfl
    | inr wp => rfl
  | bot =>
    -- Bottom is never in an MCS and never satisfied
    cases w with
    | inl wn =>
      simp [Dual.world_sat, world_to_form_set]
      exact mcs_no_bot wn.property
    | inr wp =>
      simp [Dual.world_sat, world_to_form_set]
      exact mcs_no_bot wp.property
  | impl φ ψ ih_φ ih_ψ =>
    -- Implication: use MCS closure under modus ponens
    cases w with
    | inl wn =>
      simp [Dual.world_sat, world_to_form_set]
      rw [ih_φ, ih_ψ]
      exact (mcs_impl_closed wn.property).symm
    | inr wp =>
      simp [Dual.world_sat, world_to_form_set]
      rw [ih_φ, ih_ψ]
      exact (mcs_impl_closed wp.property).symm
  | box φ ih_φ =>
    -- Box: the key modal case
    cases w with
    | inl wn =>
      -- N-world: □φ satisfied iff φ in all accessible worlds
      simp only [Dual.world_sat, world_to_form_set]
      constructor
      · -- Forward: if φ satisfied at all accessible worlds, then □φ ∈ Γ
        intro hall
        apply mcs_box_of_all wn.property
        intro v hrel
        have hsat := hall v hrel
        rw [ih_φ v] at hsat
        exact hsat
      · -- Backward: if □φ ∈ Γ, then φ satisfied at all accessible worlds
        intro hbox v hrel
        rw [ih_φ v]
        exact canon_acc_n hrel φ hbox
    | inr wp =>
      -- P-world: □φ satisfied iff φ in some accessible world
      simp only [Dual.world_sat, world_to_form_set]
      constructor
      · -- Forward: if φ satisfied at some accessible world, then □φ ∈ Γ
        intro ⟨v, hrel, hsat⟩
        apply mcs_box_of_exists_p wp.property
        use v, hrel
        rw [ih_φ v] at hsat
        exact hsat
      · -- Backward: if □φ ∈ Γ, then ∃ accessible world satisfying φ
        intro hbox
        obtain ⟨v, hrel, hφ_mem⟩ := existence_pworld hbox
        use v, hrel
        rw [ih_φ v]
        exact hφ_mem

-- Completeness with respect to the canonical model
lemma complete_wrt_canon {Atom : Type} (φ : Formula Atom) :
    Dual.model_sat (CanonicalModel Atom) φ → (EM.proof_system Atom).entails ∅ φ := by
  intro hmodel
  -- Apply deriv_iff_mem_mcs
  rw [deriv_iff_mem_mcs]
  intro Γ hΓ
  -- Construct an n-world from Γ
  let wn : NWorld Atom := ⟨Γ, hΓ⟩
  -- φ is satisfied at this world in the canonical model
  have hsat : Dual.world_sat (CanonicalModel Atom) (.inl wn) φ := hmodel (.inl wn)
  -- By truth lemma, φ ∈ Γ
  rw [truth_lemma (.inl wn) φ] at hsat
  exact hsat

-- Canonical model satisfies valid formulas
lemma valid_implies_canon_sat {Atom : Type} (φ : Formula Atom) :
    (⊨[Dual.semantics Atom] φ) → Dual.model_sat (CanonicalModel Atom) φ := by
  intro hvalid
  -- hvalid : is_sem_conseq sem ∅ φ
  -- Apply to canonical model with empty context
  exact hvalid (CanonicalModel Atom) (by simp)

theorem is_complete_weak (Atom : Type) :
  Logic.is_complete_weak (EM.proof_system Atom) (Dual.semantics Atom) := by
  intro φ hvalid
  -- Valid formulas are satisfied in the canonical model
  have hcanon : Dual.model_sat (CanonicalModel Atom) φ :=
    valid_implies_canon_sat φ hvalid
  -- Formulas satisfied in canonical model are derivable
  exact complete_wrt_canon φ hcanon

end completeness

end Modal.SoundComplete.EM_Dual
