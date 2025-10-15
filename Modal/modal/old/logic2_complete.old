import Modal.cpl.proof
import Modal.modal.formula
import Modal.modal.dual_model
import Modal.modal.logic_2
import Modal.modal.axioms_rules


open ModalFormula CPLSeq ModalAxioms

variable {α : Type}

abbrev Consistent (Γ : Multiset (ModalFormula α)) : Prop := TwoConsistent Γ

def MaximallyConsistent (Γ : Multiset (ModalFormula α)) : Prop :=
  Consistent Γ ∧
  ∀ φ, φ ∉ Γ → ¬Consistent (φ ::ₘ Γ)

def ContainsAxKN (Γ : Multiset (ModalFormula α)) : Prop :=
  (ax_K (⊤ : ModalFormula α) (⊤ : ModalFormula α)) ∈ Γ ∧
  (ax_N : ModalFormula α) ∈ Γ

-- Type abbreviations for the world types
abbrev NWorld (α : Type) := {Γ : Set (ModalFormula α) // MaximallyConsistent Γ ∧ ContainsAxKN Γ}
abbrev PWorld (α : Type) := {Γ : Set (ModalFormula α) // MaximallyConsistent Γ ∧ ¬ContainsAxKN Γ}

-- Helper to extract the set from a world
def worldSet : (NWorld α ⊕ PWorld α) → Set (ModalFormula α)
  | Sum.inl w => w.val
  | Sum.inr w => w.val

-- Define the accessibility relation for the canonical model
def CanonicalRel (w1 w2 : NWorld α ⊕ PWorld α) : Prop :=
  match w1 with
  | Sum.inl _ =>
      -- From n_world, use box formulas
      ∀ φ, (ModalFormula.box φ) ∈ worldSet w1 → φ ∈ worldSet w2
  | Sum.inr _ =>
      -- From p_world, use dia formulas
      ∀ φ, (ModalFormula.dia φ) ∈ worldSet w1 → φ ∈ worldSet w2

-- Define the valuation for the canonical model
def CanonicalVal (w : NWorld α ⊕ PWorld α) (a : α) : Prop :=
  (ModalFormula.atom a) ∈ worldSet w

-- The canonical dual model for logic_2
def CanonicalDualModel : DualModel.DualModel α := {
  frame := {
    n_world := NWorld α
    p_world := PWorld α
    rel := CanonicalRel
  }
  val := CanonicalVal
}

-- Helper: The set of all unboxed formulas from Γ
def unbox (Γ : Set (ModalFormula α)) : Set (ModalFormula α) :=
  {φ | ModalFormula.box φ ∈ Γ}

-- Helper: The set of all undia formulas from Γ
def undia (Γ : Set (ModalFormula α)) : Set (ModalFormula α) :=
  {φ | ModalFormula.dia φ ∈ Γ}

-- Lindenbaum's Lemma: Every consistent set can be extended to a maximally consistent set
-- This is a fundamental meta-theorem requiring classical logic and Zorn's lemma
-- TODO: Requires proof using Zorn's lemma in classical logic
theorem lindenbaum : ∀ {α : Type} (Γ : Set (ModalFormula α)), Consistent Γ →
  ∃ (Δ : Set (ModalFormula α)), MaximallyConsistent Δ ∧ Γ ⊆ Δ := by
  sorry

-- Characteristic axiom of logic_2: □φ ∨ ◇φ is provable for any φ
-- This holds in dual models: in n-worlds, □⊤ acts like necessitation;
--                             in p-worlds, ◇⊤ acts dually
-- Proof strategy: Use ax_KN2 which gives (... ∧ □⊤) ∨ (... ∧ ◇⊤)
theorem box_or_dia : ∀ (φ : ModalFormula α),
    TwoProof (ModalFormula.box φ ∨ ModalFormula.dia φ) := by
  intro φ
  -- Get ax_KN2 with p := ⊤ and q := φ
  -- This gives: ((□(⊤ → φ) → (□⊤ → □φ)) ∧ □⊤) ∨ ((◇(⊤ → φ) → (◇⊤ → ◇φ)) ∧ ◇⊤)
  have hKN2 := TwoProof.ax_kn2 (p := ⊤) (q := φ)

  -- Since ⊤ → φ is equivalent to φ (by CPL), we can use rl_re
  -- First, get the equivalence: ⊤ → φ ≡ φ
  have hEquiv : TwoProof ((⊤ → φ) ↔ φ) := by
    apply TwoProof.classical
    sorry  -- TODO: Prove CPL tautology (⊤ → φ) ↔ φ

  -- Apply rl_re to get: □(⊤ → φ) ↔ □φ
  have hBoxEquiv := TwoProof.rl_re hEquiv

  -- Similarly for diamond: ◇(⊤ → φ) ↔ ◇φ
  -- But we don't have a rule for diamonds directly...
  -- We need to work through the proof more carefully

  sorry

-- Maximal consistency implies closure under provable consequences (modus ponens)
theorem max_consistent_closed : ∀ (Γ : Set (ModalFormula α)) (φ ψ : ModalFormula α),
  MaximallyConsistent Γ → φ ∈ Γ → TwoProof (φ → ψ) → ψ ∈ Γ := by
  intro Γ φ ψ hMax hφ hImpl
  -- By maximal consistency, either ψ ∈ Γ or ¬ψ ∈ Γ (by maximality + excluded middle)
  by_cases h : ψ ∈ Γ
  · -- Case 1: ψ ∈ Γ, we're done
    exact h
  · -- Case 2: ψ ∉ Γ
    -- By maximality, since ψ ∉ Γ, adding ψ makes Γ inconsistent
    -- We'll derive a contradiction by showing Γ itself is inconsistent

    -- Strategy: Show that ¬ψ ∈ Γ, then use max_consistent_no_contra
    -- To show ¬ψ ∈ Γ: if ¬ψ ∉ Γ, then by maximality Γ ∪ {¬ψ} is inconsistent
    -- But we also know Γ ∪ {ψ} is inconsistent (from maximality)
    -- From these two facts and excluded middle, Γ must be inconsistent

    -- First, let's consider whether ¬ψ ∈ Γ
    by_cases hNeg : (¬ψ) ∈ Γ
    · -- ¬ψ ∈ Γ
      -- But we have φ ∈ Γ and ⊢ φ → ψ
      -- From φ and φ → ψ, we can derive ψ
      -- So we have both ψ (derivable) and ¬ψ (in Γ), contradiction

      -- We need to show this leads to inconsistency of Γ
      -- Have: φ ∈ Γ, ¬ψ ∈ Γ, and ⊢ φ → ψ
      -- From φ and φ → ψ, we get ψ (by modus ponens in CPL)
      -- From ψ and ¬ψ, we get ⊥
      -- So the list [φ, ¬ψ] proves ⊥ (using ⊢ φ → ψ)

      exfalso
      apply hMax.1
      -- Witness: [φ, ¬ψ]
      let witness := List.cons φ (List.cons (¬ψ) List.nil)
      use witness
      constructor
      · intro χ hχ
        unfold witness at hχ
        cases hχ with
        | head => exact hφ
        | tail _ hχ' =>
          cases hχ' with
          | head => exact hNeg
          | tail _ hχ'' => cases hχ''
      · -- Need to prove: TwoProof (¬conjList [φ, ¬ψ])
        -- conjList [φ, ¬ψ] = φ ∧ ¬ψ
        -- So we need: ⊢ ¬(φ ∧ ¬ψ), i.e., ⊢ φ → ψ
        -- But we have ⊢ φ → ψ as hImpl!
        unfold witness conjList
        change TwoProof (¬(φ ∧ ¬ψ))
        -- ¬(φ ∧ ¬ψ) is equivalent to φ → ψ
        -- We need to show: ⊢ φ → ψ  implies  ⊢ ¬(φ ∧ ¬ψ)
        -- This is a CPL equivalence
        sorry  -- Need CPL lemma: (φ → ψ) ↔ ¬(φ ∧ ¬ψ)

    · -- ¬ψ ∉ Γ
      -- Since Γ is maximally consistent and ¬ψ ∉ Γ, we have Γ ∪ {¬ψ} is inconsistent
      have hNegIncons := hMax.2 (¬ψ) hNeg
      -- Also, since ψ ∉ Γ, we have Γ ∪ {ψ} is inconsistent
      have hPosIncons := hMax.2 ψ h
      -- Both Γ ∪ {ψ} and Γ ∪ {¬ψ} are inconsistent
      -- This means Γ itself must be inconsistent (by excluded middle)
      -- TODO: This requires a meta-theorem about maximal consistent sets
      sorry

-- If we can derive a contradiction from Γ', we can rearrange to isolate one formula
-- TODO: Prove by list manipulation and propositional logic
theorem conj_implies_last : ∀ (Γ' : List (ModalFormula α)) (ψ : ModalFormula α),
  TwoProof (¬(conjList (Γ' ++ [ψ]))) →
  TwoProof (conjList Γ' → ¬ψ) := by
  sorry

-- Distribution of □ over conjunction: if □φ₁ ∈ Γ and □φ₂ ∈ Γ (maximally consistent),
-- then □(φ₁ ∧ φ₂) ∈ Γ
-- TODO: Prove using K axiom and maximal consistency
theorem box_conj_in_max : ∀ (Γ : Set (ModalFormula α)) (φ₁ φ₂ : ModalFormula α),
  MaximallyConsistent Γ → ModalFormula.box φ₁ ∈ Γ → ModalFormula.box φ₂ ∈ Γ →
  ModalFormula.box (φ₁ ∧ φ₂) ∈ Γ := by
  sorry

-- Helper lemma: In a maximal consistent set, if a disjunction is provable,
-- at least one disjunct must be in the set (otherwise both negations would be in it)
theorem provable_disj_in_max : ∀ (Γ : Set (ModalFormula α)) (φ ψ : ModalFormula α),
  MaximallyConsistent Γ → TwoProof (φ ∨ ψ) → (φ ∈ Γ ∨ ψ ∈ Γ) := by
  intro Γ φ ψ hMax hProof
  -- By maximal consistency, for any formula χ, either χ ∈ Γ or ¬χ ∈ Γ
  by_cases hφ : φ ∈ Γ
  · -- If φ ∈ Γ, we're done
    left
    exact hφ
  · -- If φ ∉ Γ, then by maximality, ¬φ ∈ Γ
    by_cases hψ : ψ ∈ Γ
    · -- If ψ ∈ Γ, we're done
      right
      exact hψ
    · -- If ψ ∉ Γ, then by maximality, ¬ψ ∈ Γ
      -- Now we have ¬φ ∈ Γ and ¬ψ ∈ Γ
      -- We also have ⊢ φ ∨ ψ
      -- From ⊢ φ ∨ ψ and ¬φ and ¬ψ, we can derive ⊥
      -- This contradicts consistency of Γ
      exfalso

      -- We need to show Γ is inconsistent
      apply hMax.1

      -- The witness is [¬φ, ¬ψ]
      use (List.cons (¬φ) (List.cons (¬ψ) List.nil))
      constructor
      · -- All formulas in the list are in Γ
        intro χ hχ
        cases hχ with
        | head =>
          -- χ = ¬φ
          -- We need to show (¬φ) ∈ Γ
          -- By maximality, since φ ∉ Γ, we have (¬φ) ∈ Γ
          sorry  -- Need: maximality implies excluded middle in Γ
        | tail _ hχ' =>
          cases hχ' with
          | head =>
            -- χ = ¬ψ
            sorry  -- Same as above: need maximality implies excluded middle
          | tail _ hχ'' => cases hχ''
      · -- Show ⊢ ¬(¬φ ∧ ¬ψ)
        -- conjList [¬φ, ¬ψ] = ¬φ ∧ ¬ψ
        -- We need ⊢ ¬(¬φ ∧ ¬ψ), which is equivalent to ⊢ φ ∨ ψ
        -- And we have ⊢ φ ∨ ψ from hProof!
        sorry  -- Need CPL lemma: ¬(¬φ ∧ ¬ψ) ↔ (φ ∨ ψ)

-- Extension to lists: if all □φᵢ are in Γ, then □(∧φᵢ) ∈ Γ
-- Proof by induction on list using box_conj_in_max
theorem box_conjList_in_max : ∀ (Γ : Set (ModalFormula α)) (Γ' : List (ModalFormula α)),
  MaximallyConsistent Γ →
  (∀ φ, φ ∈ Γ' → ModalFormula.box φ ∈ Γ) →
  ModalFormula.box (conjList Γ') ∈ Γ := by
  intro Γ Γ' hMax hAll
  -- Induction on the list Γ'
  induction Γ' with
  | nil =>
    -- Base case: Γ' = []
    -- conjList [] = ⊤
    -- Need to show: □⊤ ∈ Γ
    -- From box_or_dia: ⊢ □⊤ ∨ ◇⊤
    have hDisj : TwoProof (ModalFormula.box (⊤ : ModalFormula α) ∨
                           ModalFormula.dia (⊤ : ModalFormula α)) :=
      @box_or_dia α (⊤ : ModalFormula α)
    -- By provable_disj_in_max, at least one of □⊤ or ◇⊤ is in Γ
    have hInMax := provable_disj_in_max Γ (ModalFormula.box ⊤)
                                        (ModalFormula.dia ⊤) hMax hDisj
    cases hInMax with
    | inl hBox =>
      -- □⊤ ∈ Γ, which is what we need
      exact hBox
    | inr hDia =>
      -- ◇⊤ ∈ Γ
      -- But we also have □⊤ ∈ Γ must hold, otherwise we'd derive a contradiction
      -- Actually, let's try a different approach: show that □⊤ must be in any consistent set
      -- Or better: if ◇⊤ ∈ Γ, can we derive □⊤ ∈ Γ?
      -- Actually, both □⊤ and ◇⊤ should be in every maximal consistent set!
      sorry  -- Need to show: if ◇⊤ ∈ Γ then also □⊤ ∈ Γ (or derive it another way)
  | cons head tail ih =>
    -- Inductive case: Γ' = head :: tail
    cases tail with
    | nil =>
      -- Γ' = [head]
      -- conjList [head] = head
      -- Need: □head ∈ Γ
      -- This follows from hAll
      simp [conjList]  -- Simplify conjList [head] = head
      apply hAll
      simp
    | cons head2 tail2 =>
      -- Γ' = head :: head2 :: tail2
      -- conjList (head :: head2 :: tail2) = head ∧ conjList (head2 :: tail2)
      -- By IH: □(conjList (head2 :: tail2)) ∈ Γ
      -- By hAll: □head ∈ Γ
      -- By box_conj_in_max: □(head ∧ conjList (head2 :: tail2)) ∈ Γ
      have hHead : ModalFormula.box head ∈ Γ := by
        apply hAll
        simp
      have hTail : ModalFormula.box (conjList (head2 :: tail2)) ∈ Γ := by
        apply ih
        intro φ hφ
        apply hAll
        simp [hφ]
      apply box_conj_in_max
      · exact hMax
      · exact hHead
      · exact hTail

-- Maximal consistency and negation: φ ∈ Γ and ¬φ ∈ Γ leads to contradiction
theorem max_consistent_no_contra : ∀ (Γ : Set (ModalFormula α)) (φ : ModalFormula α),
  MaximallyConsistent Γ → φ ∈ Γ → (¬φ) ∈ Γ → False := by
  intro Γ φ hMax hφ hNotφ
  -- Γ is consistent, meaning ¬(Γ ⊢₂ ⊥)
  have hCons := hMax.1
  -- We'll show Γ ⊢₂ ⊥, contradicting consistency
  apply hCons
  -- Use CPL sequent calculus to derive ⊥ from {φ, ¬φ}
  let witness := List.cons φ (List.cons (¬φ) List.nil)
  apply TwoDerivable.classical witness
  · -- Show witness ⊆ Γ
    intro ψ hψ
    cases hψ with
    | head => exact hφ
    | tail _ hψ' =>
      cases hψ' with
      | head => exact hNotφ
      | tail _ hψ'' => cases hψ''
  · -- Prove: φ, ¬φ ⊢ ⊥ in sequent calculus
    -- ¬φ is φ → ⊥, so we have φ and φ → ⊥ on the left
    -- We need to derive ⊥ on the right
    sorry  -- TODO: Prove {φ, φ → ⊥} ⊢ ⊥ in CPL sequent calculus
      · apply Multiset.mem_cons_self
      · apply Multiset.mem_cons_self
    -- Now apply neg_l to get: (¬φ) ::ₘ φ ::ₘ ∅ ⊢ ∅
    have h2 := CPLSeqProof.neg_l h
    -- We have φ ::ₘ (¬φ) ::ₘ ∅ but need (¬φ) ::ₘ φ ::ₘ ∅
    -- Multisets are unordered, so these are equal
    have heq : φ ::ₘ (¬φ) ::ₘ ∅ = (¬φ) ::ₘ φ ::ₘ ∅ := by
      rw [Multiset.cons_swap]
    rw [heq]
    exact h2

-- ax_def_dia in maximally consistent sets: ◇φ ∈ Γ iff ¬□¬φ ∈ Γ
theorem dia_iff_not_box_not : ∀ (Γ : Set (ModalFormula α)) (φ : ModalFormula α),
  MaximallyConsistent Γ →
  (ModalFormula.dia φ ∈ Γ ↔ ¬(ModalFormula.box (¬φ) ∈ Γ)) := by
  intro Γ φ hMax
  constructor
  · -- Forward direction: ◇φ ∈ Γ → ¬(□¬φ ∈ Γ)
    intro hDia
    -- Suppose □¬φ ∈ Γ for contradiction
    intro hBox
    -- We have both ◇φ ∈ Γ and □¬φ ∈ Γ
    -- But ax_def_dia says ◇φ ↔ ¬□¬φ, so ◇φ and □¬φ contradict each other
    -- From ◇φ ↔ ¬□¬φ, we get ◇φ → ¬□¬φ
    -- So from ◇φ, we can derive ¬□¬φ
    -- This means ¬□¬φ ∈ Γ (by max_consistent_closed)
    have hImpl : TwoProof (ModalFormula.dia φ → ¬(ModalFormula.box (¬φ))) := by
      -- From ax_def_dia: ◇φ ↔ ¬□¬φ, extract the forward implication
      have hBiImpl := TwoProof.ax_def_dia (p := φ)
      -- Need to extract (◇φ → ¬□¬φ) from (◇φ ↔ ¬□¬φ)
      -- This requires a CPL lemma about extracting implications from biconditionals
      sorry
    have hNotBox : (¬ModalFormula.box (¬φ)) ∈ Γ :=
      max_consistent_closed Γ (ModalFormula.dia φ) (¬ModalFormula.box (¬φ)) hMax hDia hImpl
    -- Now we have both □¬φ ∈ Γ and ¬□¬φ ∈ Γ, contradiction
    exact max_consistent_no_contra Γ (ModalFormula.box (¬φ)) hMax hBox hNotBox

  · -- Backward direction: ¬(□¬φ ∈ Γ) → ◇φ ∈ Γ
    intro hNotBox
    -- We need to show ◇φ ∈ Γ
    -- By maximality, either ◇φ ∈ Γ or ◇φ ∉ Γ
    by_cases h : ModalFormula.dia φ ∈ Γ
    · exact h
    · -- ◇φ ∉ Γ, so by maximality, Γ ∪ {◇φ} is inconsistent
      -- We'll show this leads to a contradiction
      -- From ax_def_dia: ◇φ ↔ ¬□¬φ, we get ¬□¬φ → ◇φ
      -- So if ¬□¬φ, then ◇φ
      -- Since ¬(□¬φ ∈ Γ) and Γ is maximal, we should have ¬□¬φ ∈ Γ
      -- Then from ¬□¬φ → ◇φ and max_consistent_closed, we get ◇φ ∈ Γ

      -- First show: ¬□¬φ ∈ Γ
      -- Since □¬φ ∉ Γ and Γ is maximally consistent, either ¬□¬φ ∈ Γ or...
      by_cases hNeg : (¬ModalFormula.box (¬φ)) ∈ Γ
      · -- ¬□¬φ ∈ Γ
        -- From ax_def_dia: ¬□¬φ → ◇φ (backward direction of biconditional)
        have hImpl : TwoProof ((¬ModalFormula.box (¬φ)) → ModalFormula.dia φ) := by
          -- From ax_def_dia: ◇φ ↔ ¬□¬φ, extract the backward implication
          have hBiImpl := TwoProof.ax_def_dia (p := φ)
          -- Need to extract (¬□¬φ → ◇φ) from (◇φ ↔ ¬□¬φ)
          sorry
        have hDiaInΓ : ModalFormula.dia φ ∈ Γ :=
          max_consistent_closed Γ (¬ModalFormula.box (¬φ)) (ModalFormula.dia φ) hMax hNeg hImpl
        -- But this contradicts h : ◇φ ∉ Γ
        contradiction
      · -- ¬□¬φ ∉ Γ
        -- So by maximality, both ◇φ ∉ Γ and ¬◇φ ∈ Γ? No, that's not quite right.
        -- Actually: ¬□¬φ ∉ Γ means by maximality that □¬φ should be in Γ
        -- But we assumed ¬(□¬φ ∈ Γ), contradiction!
        -- Wait, let me reconsider: hNotBox says □¬φ ∉ Γ
        -- hNeg says ¬□¬φ ∉ Γ
        -- By excluded middle and maximality, one of {□¬φ, ¬□¬φ} should be in Γ
        -- TODO: Need a lemma about maximally consistent sets and excluded middle
        sorry

-- Key theorem for n-worlds: if a list from unbox(Γ) ∪ {B} derives ⊥, then □¬B ∈ Γ
-- This requires Γ to be a K-theory (n-world) to use K axiom and necessitation
-- Proof strategy (from existence lemma proof):
--   1. Have: ⊢ ¬(conjList Γ'), where Γ' ⊆ unbox(Γ) ∪ {B}
--   2. Rearrange: ⊢ (conjList Γ'') → ¬B (where Γ'' is formulas from unbox(Γ))
--   3. For each φ ∈ Γ'', have □φ ∈ Γ
--   4. Use K axiom repeatedly: □(conjList Γ'') ∈ Γ
--   5. Apply necessitation to theorem: ⊢ □((conjList Γ'') → ¬B)
--   6. Use K axiom: □(conjList Γ'' → ¬B) ∧ □(conjList Γ'') → □¬B
--   7. By modus ponens (in K-theory): □¬B ∈ Γ
theorem inconsistency_implies_box_neg :
  ∀ (Γ : Set (ModalFormula α)) (Γ' : List (ModalFormula α)) (B : ModalFormula α),
  MaximallyConsistent Γ → ContainsAxKN Γ →  -- Γ must be an n-world (K-theory)
  (∀ φ, φ ∈ Γ' → φ ∈ unbox Γ ∨ φ = B) →
  TwoProof (¬conjList Γ') →
  ModalFormula.box (¬B) ∈ Γ := by
  sorry

-- Dual theorem for p-worlds: if a list from undia(Γ) ∪ {B} derives ⊥, then ◇¬B ∈ Γ
-- For p-worlds, we can't use K axiom directly, so different strategy needed
-- Strategy: Use ax_def_dia and box_or_dia
--   1. Have: ⊢ ¬(conjList Γ'), where Γ' ⊆ undia(Γ) ∪ {B}
--   2. Rearrange: ⊢ (conjList Γ'') → ¬B (where Γ'' is formulas from undia(Γ))
--   3. By box_or_dia: either □¬B ∈ Γ or ◇¬B ∈ Γ
--   4. If □¬B ∈ Γ, then by ax_def_dia: ¬◇B ∈ Γ
--   5. Need to show this contradicts the consistency requirement
--   TODO: Work out the exact argument for p-worlds
theorem inconsistency_implies_dia_neg :
  ∀ (Γ : Set (ModalFormula α)) (Γ' : List (ModalFormula α)) (B : ModalFormula α),
  MaximallyConsistent Γ → ¬ContainsAxKN Γ →  -- Γ must be a p-world (not K-theory)
  (∀ φ, φ ∈ Γ' → φ ∈ undia Γ ∨ φ = B) →
  TwoProof (¬conjList Γ') →
  ModalFormula.dia (¬B) ∈ Γ := by
  sorry

-- Box formula interdefinability: □φ ∈ Γ iff ¬◇¬φ ∈ Γ in maximally consistent sets
-- TODO: Prove using dual of dia_iff_not_box_not
theorem box_iff_not_dia_not : ∀ (Γ : Set (ModalFormula α)) (φ : ModalFormula α),
  MaximallyConsistent Γ →
  (ModalFormula.box φ ∈ Γ ↔ ¬(ModalFormula.dia (¬φ) ∈ Γ)) := by
  sorry

-- Key lemma: If ◇B ∈ Γ and Γ is maximally consistent n-world, then unbox(Γ) ∪ {B} is consistent
lemma unbox_dia_consistent (Γ : Set (ModalFormula α)) (B : ModalFormula α)
    (hMax : MaximallyConsistent Γ) (hKN : ContainsAxKN Γ) (hDia : ModalFormula.dia B ∈ Γ) :
    Consistent (unbox Γ ∪ {B}) := by
  -- Proof by contradiction
  intro hIncons
  -- There exists a finite list from unbox(Γ) ∪ {B} that derives a contradiction
  obtain ⟨Γ', hSub, hProof⟩ := hIncons

  -- By our axiom, this inconsistency implies □¬B ∈ Γ
  have hBoxNotB : ModalFormula.box (¬B) ∈ Γ :=
    inconsistency_implies_box_neg Γ Γ' B hMax hKN hSub hProof

  -- But ◇B ∈ Γ means ¬(□¬B) ∈ Γ by ax_def_dia
  have hNotBoxNotB : ¬(ModalFormula.box (¬B) ∈ Γ) :=
    (dia_iff_not_box_not Γ B hMax).mp hDia

  -- Contradiction!
  exact hNotBoxNotB hBoxNotB

-- Dual lemma: If □B ∈ Γ and Γ is maximally consistent p-world, then undia(Γ) ∪ {B} is consistent
lemma undia_box_consistent (Γ : Set (ModalFormula α)) (B : ModalFormula α)
    (hMax : MaximallyConsistent Γ) (hNotKN : ¬ContainsAxKN Γ) (hBox : ModalFormula.box B ∈ Γ) :
    Consistent (undia Γ ∪ {B}) := by
  -- Proof by contradiction
  intro hIncons
  -- There exists a finite list from undia(Γ) ∪ {B} that derives a contradiction
  obtain ⟨Γ', hSub, hProof⟩ := hIncons

  -- By our axiom, this inconsistency implies ◇¬B ∈ Γ
  have hDiaNotB : ModalFormula.dia (¬B) ∈ Γ :=
    inconsistency_implies_dia_neg Γ Γ' B hMax hNotKN hSub hProof

  -- But □B ∈ Γ means ¬(◇¬B) ∈ Γ by box_iff_not_dia_not
  have hNotDiaNotB : ¬(ModalFormula.dia (¬B) ∈ Γ) :=
    (box_iff_not_dia_not Γ B hMax).mp hBox

  -- Contradiction!
  exact hNotDiaNotB hDiaNotB

-- Existence Lemma for n-worlds (negative worlds)
-- If ◇B is in an n-world Γ, then there exists an accessible world Δ such that B ∈ Δ
theorem existence_nworld (Γ : NWorld α) (B : ModalFormula α) (h : ModalFormula.dia B ∈ Γ.val) :
    ∃ (Δ : NWorld α ⊕ PWorld α), CanonicalRel (Sum.inl Γ) Δ ∧ B ∈ worldSet Δ := by
  -- Construct the candidate set
  let Γ' := unbox Γ.val ∪ {B}

  -- Show Γ' is consistent
  have hCons : Consistent Γ' := unbox_dia_consistent Γ.val B Γ.property.1 Γ.property.2 h

  -- Extend to maximally consistent set using Lindenbaum
  obtain ⟨Δ, hMaxΔ, hSub⟩ := lindenbaum Γ' hCons

  -- Determine if Δ is an n-world or p-world
  by_cases hContains : ContainsAxKN Δ
  · -- Δ is an n-world
    let ΔWorld : NWorld α := Subtype.mk Δ (And.intro hMaxΔ hContains)
    use Sum.inl ΔWorld
    constructor
    · -- Show CanonicalRel holds
      intro φ hBox
      -- If □φ ∈ Γ, then φ ∈ unbox(Γ), so φ ∈ Γ', so φ ∈ Δ
      have : φ ∈ Γ' := Or.inl hBox
      exact hSub this
    · -- Show B ∈ Δ
      apply hSub
      exact Or.inr rfl
  · -- Δ is a p-world
    let ΔWorld : PWorld α := Subtype.mk Δ (And.intro hMaxΔ hContains)
    use Sum.inr ΔWorld
    constructor
    · -- Show CanonicalRel holds
      intro φ hBox
      have : φ ∈ Γ' := Or.inl hBox
      exact hSub this
    · -- Show B ∈ Δ
      apply hSub
      exact Or.inr rfl

-- Existence Lemma for p-worlds (positive worlds)
-- If □B is in a p-world Γ, then there exists an accessible world Δ such that B ∈ Δ
theorem existence_pworld (Γ : PWorld α) (B : ModalFormula α)
    (h : ModalFormula.box B ∈ Γ.val) :
    ∃ (Δ : NWorld α ⊕ PWorld α), CanonicalRel (Sum.inr Γ) Δ ∧ B ∈ worldSet Δ := by
  -- Construct the candidate set (using undia instead of unbox)
  let Γ' := undia Γ.val ∪ {B}

  -- Show Γ' is consistent (dual of unbox_dia_consistent)
  have hCons : Consistent Γ' := undia_box_consistent Γ.val B Γ.property.1 Γ.property.2 h

  -- Extend to maximally consistent set using Lindenbaum
  obtain ⟨Δ, hMaxΔ, hSub⟩ := lindenbaum Γ' hCons

  -- Determine if Δ is an n-world or p-world
  by_cases hContains : ContainsAxKN Δ
  · -- Δ is an n-world
    let ΔWorld : NWorld α := Subtype.mk Δ (And.intro hMaxΔ hContains)
    use Sum.inl ΔWorld
    constructor
    · -- Show CanonicalRel holds (for p-world source, check dia formulas)
      intro φ hDia
      -- If ◇φ ∈ Γ, then φ ∈ undia(Γ), so φ ∈ Γ', so φ ∈ Δ
      have : φ ∈ Γ' := Or.inl hDia
      exact hSub this
    · -- Show B ∈ Δ
      apply hSub
      exact Or.inr rfl
  · -- Δ is a p-world
    let ΔWorld : PWorld α := Subtype.mk Δ (And.intro hMaxΔ hContains)
    use Sum.inr ΔWorld
    constructor
    · -- Show CanonicalRel holds (for p-world source, check dia formulas)
      intro φ hDia
      have : φ ∈ Γ' := Or.inl hDia
      exact hSub this
    · -- Show B ∈ Δ
      apply hSub
      exact Or.inr rfl

open DualModel

-- Truth Lemma: A formula φ is satisfied at a world w in the canonical model
-- if and only if φ is in the set of formulas that defines w
-- This is the key lemma connecting syntax (formulas in sets) with semantics (satisfaction)
-- TODO: The proof proceeds by induction on φ, using the existence lemmas for modal cases
theorem truth_lemma : ∀ (w : NWorld α ⊕ PWorld α) (φ : ModalFormula α),
    world_sat CanonicalDualModel w φ ↔ φ ∈ worldSet w := by
  sorry

-- If φ is not provable, then {¬φ} is consistent
-- This is essentially the contrapositive of soundness
-- TODO: This follows from soundness theorem
theorem unprovable_consistent : ∀ {α : Type} (φ : ModalFormula α),
  ¬TwoProof φ → Consistent {¬φ} := by
  sorry

theorem logic_2_complete :
    ∀ (φ : ModalFormula α), dual_valid φ → TwoProof φ := by
  intro φ h_valid
  -- Proof by contrapositive: assume ¬TwoProof φ, derive ¬dual_valid φ
  by_contra h_not_proof

  -- If φ is not provable, then {¬φ} is consistent
  have h_cons : Consistent {¬φ} := unprovable_consistent φ h_not_proof

  -- Extend {¬φ} to a maximally consistent set Γ₀
  obtain ⟨Γ₀, hMax₀, hSub₀⟩ := lindenbaum {¬φ} h_cons

  -- We have ¬φ ∈ Γ₀
  have h_neg_phi : (¬φ) ∈ Γ₀ := hSub₀ rfl

  -- Determine whether Γ₀ is an n-world or p-world
  by_cases hContains : ContainsAxKN Γ₀
  · -- Case 1: Γ₀ is an n-world
    let w₀ : NWorld α := Subtype.mk Γ₀ (And.intro hMax₀ hContains)

    -- By truth lemma, ¬φ is satisfied at w₀ in the canonical model
    have h_neg_sat : world_sat CanonicalDualModel (Sum.inl w₀) (¬φ) :=
      (truth_lemma (Sum.inl w₀) (¬φ)).mpr h_neg_phi

    -- This means φ is not satisfied at w₀
    rw [world_sat_neg] at h_neg_sat

    -- But h_valid says φ is valid in all dual models, including the canonical model
    -- So φ must be satisfied at all worlds in the canonical model
    have h_sat : world_sat CanonicalDualModel (Sum.inl w₀) φ := by
      -- dual_valid means: ∀ frame, ∀ valuation, ∀ world, φ is satisfied
      have h1 : frame_sat (@CanonicalDualModel α).frame φ := h_valid (@CanonicalDualModel α).frame
      unfold frame_sat at h1
      have h2 : model_sat (@CanonicalDualModel α) φ := h1 (@CanonicalDualModel α).val
      unfold model_sat at h2
      exact h2 (Sum.inl w₀)

    -- Contradiction!
    exact h_neg_sat h_sat

  · -- Case 2: Γ₀ is a p-world
    let w₀ : PWorld α := Subtype.mk Γ₀ (And.intro hMax₀ hContains)

    -- By truth lemma, ¬φ is satisfied at w₀ in the canonical model
    have h_neg_sat : world_sat CanonicalDualModel (Sum.inr w₀) (¬φ) :=
      (truth_lemma (Sum.inr w₀) (¬φ)).mpr h_neg_phi

    -- This means φ is not satisfied at w₀
    rw [world_sat_neg] at h_neg_sat

    -- But h_valid says φ is valid in all dual models
    have h_sat : world_sat CanonicalDualModel (Sum.inr w₀) φ := by
      have h1 : frame_sat (@CanonicalDualModel α).frame φ := h_valid (@CanonicalDualModel α).frame
      unfold frame_sat at h1
      have h2 : model_sat (@CanonicalDualModel α) φ := h1 (@CanonicalDualModel α).val
      unfold model_sat at h2
      exact h2 (Sum.inr w₀)

    -- Contradiction!
    exact h_neg_sat h_sat
