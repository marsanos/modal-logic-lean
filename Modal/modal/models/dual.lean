import Modal.modal.formula
import Modal.cpl.syntax


namespace Dual

open ModalFormula CPLSyntax


-- α is the set of atomic propositions
structure Frame where
  n_world : Type
  p_world : Type
  rel : (n_world ⊕ p_world) → (n_world ⊕ p_world) → Prop

abbrev Frame.world (F : Frame) := F.n_world ⊕ F.p_world

structure Model (α : Type) where
  frame : Frame
  val : frame.world → α → Prop



variable {α : Type}

-- Defines truth at a specific world w, that is m, w ⊨ φ.
def world_sat (m : Model α) (w : m.frame.world) : ModalFormula α → Prop
  | .atom a => m.val w a
  | .bot => False
  | .impl φ ψ => world_sat m w φ → world_sat m w ψ
  | .box φ => match w with
    | .inl wn => ∀ v, (m.frame.rel (.inl wn) v) → world_sat m v φ
    | .inr wp => ∃ v, (m.frame.rel (.inr wp) v) ∧ (world_sat m v φ)
  | .dia φ => match w with
    | .inl wn => ∃ v, (m.frame.rel (.inl wn) v) ∧ (world_sat m v φ)
    | .inr wp => ∀ v, (m.frame.rel (.inr wp) v) → (world_sat m v φ)

-- Defines truth in an entire model m, that is m ⊨ φ.
def model_sat (m : Model α) (φ : ModalFormula α) : Prop :=
  ∀ w, world_sat m w φ

-- Defines truth in an entire model f, that is f ⊨ φ.
def frame_sat (f : Frame) (φ : ModalFormula α) : Prop :=
  ∀ val, model_sat ⟨f, val⟩ φ

-- Defines truth in all possible models, that is ⊨ φ.
def valid (φ : ModalFormula α) : Prop :=
  ∀ (f : Frame), frame_sat f φ

-- Defines truth in all frames satisfying a given class/property.
def valid_in_class (P : Frame → Prop) (φ : ModalFormula α) : Prop :=
  ∀ (f : Frame), P f → frame_sat f φ




-- some derived results that may be useful later

theorem world_sat_neg {m : Model α} {w : m.frame.world} {φ : ModalFormula α} :
    world_sat m w (¬φ) ↔ ¬(world_sat m w φ) := by
  constructor
  · intro h hsat
    exact h hsat
  · intro h hsat
    exact h hsat

theorem world_sat_top {m : Model α} {w : m.frame.world} :
    world_sat m w ⊤ := by
  unfold top neg
  simp [world_sat]

theorem world_sat_or {m : Model α} {w : m.frame.world} {φ ψ : ModalFormula α} :
    world_sat m w (φ ∨ ψ) ↔ (world_sat m w φ ∨ world_sat m w ψ) := by
  unfold CPLSyntax.or CPLSyntax.neg
  simp [world_sat]
  constructor
  · intro h
    cases Classical.em (world_sat m w φ) with
    | inl hp => exact Or.inl hp
    | inr hnp => exact Or.inr (h hnp)
  · intro h hnp
    cases h with
    | inl hp => contradiction
    | inr hq => exact hq

theorem world_sat_and {m : Model α} {w : m.frame.world} {φ ψ : ModalFormula α} :
    world_sat m w (φ ∧ ψ) ↔ (world_sat m w φ ∧ world_sat m w ψ) := by
  unfold CPLSyntax.and CPLSyntax.neg
  simp only [world_sat]
  -- After unfolding: (world_sat m w φ → world_sat m w ψ → False) → False ↔ (world_sat m w φ ∧ world_sat m w ψ)
  constructor
  · intro h
    -- h : (world_sat m w φ → world_sat m w ψ → False) → False
    constructor
    · -- Prove world_sat m w φ
      cases Classical.em (world_sat m w φ) with
      | inl h_phi => exact h_phi
      | inr h_neg_phi =>
        exfalso
        apply h
        intro h_phi _
        exact h_neg_phi h_phi
    · -- Prove world_sat m w ψ
      cases Classical.em (world_sat m w ψ) with
      | inl h_psi => exact h_psi
      | inr h_neg_psi =>
        exfalso
        apply h
        intro h_phi h_psi
        exact h_neg_psi h_psi
  · intro ⟨h_phi, h_psi⟩
    -- We have both world_sat m w φ and world_sat m w ψ
    -- We need to prove (world_sat m w φ → world_sat m w ψ → False) → False
    intro h_impl
    exact h_impl h_phi h_psi

theorem world_sat_iff {m : Model α} {w : m.frame.world} {φ ψ : ModalFormula α} :
    world_sat m w (φ ↔ ψ) ↔ (world_sat m w φ ↔ world_sat m w ψ) := by
  unfold CPLSyntax.iff
  -- φ ↔ ψ = (φ → ψ) ∧ (ψ → φ)
  rw [world_sat_and]
  -- Now we have: world_sat m w (φ → ψ) ∧ world_sat m w (ψ → φ) ↔ (world_sat m w φ ↔ world_sat m w ψ)
  simp only [world_sat]
  constructor
  · intro ⟨h_forward, h_backward⟩
    -- h_forward : world_sat m w φ → world_sat m w ψ
    -- h_backward : world_sat m w ψ → world_sat m w φ
    constructor
    · exact h_forward
    · exact h_backward
  · intro h_iff
    constructor
    · exact h_iff.mp
    · exact h_iff.mpr


end Dual
