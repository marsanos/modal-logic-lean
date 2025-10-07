import Modal.cpl.proof
import Modal.modal.formula
import Modal.modal.dual_model
import Modal.modal.logic_2


open ModalFormula DualModel CPLSeq

variable {α : Type}


private def seqValid (Γ Δ : Multiset (ModalFormula α)) : Prop :=
  ∀ (m : DualModel α) (w : m.frame.world),
    (∀ A, A ∈ Γ → world_sat m w A) →
    (∃ B, B ∈ Δ ∧ world_sat m w B)

private lemma cplSeqProof_sound {s : Sequent (ModalFormula α)}
    (h : CPLSeqProof s) : seqValid s.left s.right := by
  classical
  induction h with
  | identity hLeft hRight =>
      intro m w hAssume
      apply Exists.intro _
      apply And.intro hRight
      exact hAssume _ hLeft
  | @and_l Γ Δ A B h ih =>
      intro m w hΓ
      dsimp at ih
      have hAnd : world_sat m w (A ∧ B) := hΓ _ (by simp)
      have hA : world_sat m w A := (world_sat_and).1 hAnd |>.1
      have hB : world_sat m w B := (world_sat_and).1 hAnd |>.2
      have hΓtail : ∀ φ, φ ∈ Γ → world_sat m w φ :=
        by
          intro φ hφ
          exact hΓ _ (by simp [hφ])
      have hAssumption : ∀ φ, φ ∈ A ::ₘ B ::ₘ Γ → world_sat m w φ := by
        intro φ hφ
        rcases Multiset.mem_cons.1 hφ with hφ | hφ
        · simpa [hφ] using hA
        · rcases Multiset.mem_cons.1 hφ with hφ | hφ
          · simpa [hφ] using hB
          · exact hΓtail _ hφ
      exact ih m w hAssumption
  | @and_r Γ Δ A B hA hB ihA ihB =>
      intro m w hΓ
      dsimp at ihA ihB
      obtain ⟨φ₁, hφ₁, hsat₁⟩ := ihA m w hΓ
      rcases Multiset.mem_cons.1 hφ₁ with hφ₁ | hφ₁
      · have hAtrue : world_sat m w A := by simpa [hφ₁] using hsat₁
        obtain ⟨φ₂, hφ₂, hsat₂⟩ := ihB m w hΓ
        rcases Multiset.mem_cons.1 hφ₂ with hφ₂ | hφ₂
        · have hBtrue : world_sat m w B := by simpa [hφ₂] using hsat₂
          apply Exists.intro (A ∧ B)
          apply And.intro (by simp)
          exact (world_sat_and).2 (And.intro hAtrue hBtrue)
        · apply Exists.intro φ₂
          exact And.intro (by simp [hφ₂]) hsat₂
      · apply Exists.intro φ₁
        exact And.intro (by simp [hφ₁]) hsat₁
  | @or_l Γ Δ A B hA hB ihA ihB =>
      intro m w hΓ
      dsimp at ihA ihB
      have hOr : world_sat m w (A ∨ B) := hΓ _ (by simp)
      have hΓtail : ∀ φ, φ ∈ Γ → world_sat m w φ :=
        by
          intro φ hφ
          exact hΓ _ (by simp [hφ])
      cases (world_sat_or).1 hOr with
      | inl hAtrue =>
          have hAssumption : ∀ φ, φ ∈ A ::ₘ Γ → world_sat m w φ := by
            intro φ hφ
            rcases Multiset.mem_cons.1 hφ with hφ | hφ
            · simpa [hφ] using hAtrue
            · exact hΓtail _ hφ
          exact ihA m w hAssumption
      | inr hBtrue =>
          have hAssumption : ∀ φ, φ ∈ B ::ₘ Γ → world_sat m w φ := by
            intro φ hφ
            rcases Multiset.mem_cons.1 hφ with hφ | hφ
            · simpa [hφ] using hBtrue
            · exact hΓtail _ hφ
          exact ihB m w hAssumption
  | @or_r Γ Δ A B h ih =>
      intro m w hΓ
      dsimp at ih
      obtain ⟨φ, hφ, hsat⟩ := ih m w hΓ
      rcases Multiset.mem_cons.1 hφ with hφ | hφ
      · have hA : world_sat m w A := by simpa [hφ] using hsat
        apply Exists.intro (A ∨ B)
        exact And.intro (by simp) ((world_sat_or).2 (Or.inl hA))
      · rcases Multiset.mem_cons.1 hφ with hφ | hφ
        · have hB : world_sat m w B := by simpa [hφ] using hsat
          apply Exists.intro (A ∨ B)
          exact And.intro (by simp) ((world_sat_or).2 (Or.inr hB))
        · apply Exists.intro φ
          exact And.intro (by simp [hφ]) hsat
  | @impl_l Γ Δ A B hA hB ihA ihB =>
      intro m w hΓ
      dsimp at ihA ihB
      have hImp : world_sat m w (A → B) := hΓ _ (by simp)
      have hΓtail : ∀ φ, φ ∈ Γ → world_sat m w φ :=
        by
          intro φ hφ
          exact hΓ _ (by simp [hφ])
      obtain ⟨φ, hφ, hsat⟩ := ihA m w hΓtail
      rcases Multiset.mem_cons.1 hφ with hφ | hφ
      · have hAtrue : world_sat m w A := by simpa [hφ] using hsat
        have hBtrue : world_sat m w B := hImp hAtrue
        have hAssumption : ∀ φ, φ ∈ B ::ₘ Γ → world_sat m w φ := by
          intro ψ hψ
          rcases Multiset.mem_cons.1 hψ with hψ | hψ
          · simpa [hψ] using hBtrue
          · exact hΓtail _ hψ
        obtain ⟨ψ, hψ, hsatψ⟩ := ihB m w hAssumption
        apply Exists.intro ψ
        exact And.intro hψ hsatψ
      · apply Exists.intro _
        exact And.intro hφ hsat
  | @impl_r Γ Δ A B h ih =>
      intro m w hΓ
      dsimp at ih
      classical
      by_cases hA : world_sat m w A
      · have hAssumption : ∀ φ, φ ∈ A ::ₘ Γ → world_sat m w φ := by
          intro φ hφ
          rcases Multiset.mem_cons.1 hφ with hφ | hφ
          · simpa [hφ] using hA
          · exact hΓ _ hφ
        obtain ⟨φ, hφ, hsatφ⟩ := ih m w hAssumption
        rcases Multiset.mem_cons.1 hφ with hφ | hφ
        · have hB : world_sat m w B := by simpa [hφ] using hsatφ
          apply Exists.intro (A → B)
          apply And.intro (by simp)
          intro _; exact hB
        · apply Exists.intro φ
          exact And.intro (by simp [hφ]) hsatφ
      · apply Exists.intro (A → B)
        apply And.intro (by simp)
        intro hA'
        exact (False.elim (hA hA') : world_sat m w B)
  | @neg_l Γ Δ A h ih =>
      intro m w hΓ
      dsimp at ih
      have hNeg : world_sat m w (¬A) := hΓ _ (by simp)
      have hNotA : ¬ world_sat m w A := (world_sat_neg).1 hNeg
      have hΓtail : ∀ φ, φ ∈ Γ → world_sat m w φ :=
        by
          intro φ hφ
          exact hΓ _ (by simp [hφ])
      obtain ⟨φ, hφ, hsatφ⟩ := ih m w hΓtail
      rcases Multiset.mem_cons.1 hφ with hφ | hφ
      · have hAtrue : world_sat m w A := by simpa [hφ] using hsatφ
        exact (False.elim (hNotA hAtrue) : ∃ B, B ∈ Δ ∧ world_sat m w B)
      · apply Exists.intro _
        exact And.intro hφ hsatφ
  | @neg_r Γ Δ A h ih =>
      intro m w hΓ
      dsimp at ih
      classical
      by_cases hA : world_sat m w A
      · have hAssumption : ∀ φ, φ ∈ A ::ₘ Γ → world_sat m w φ := by
          intro φ hφ
          rcases Multiset.mem_cons.1 hφ with hφ | hφ
          · simpa [hφ] using hA
          · exact hΓ _ hφ
        obtain ⟨φ, hφ, hsatφ⟩ := ih m w hAssumption
        apply Exists.intro φ
        exact And.intro (by simp [hφ]) hsatφ
      · apply Exists.intro (¬A)
        apply And.intro (by simp)
        exact (world_sat_neg).2 hA


theorem logic_2_sound :
    ∀ (φ : ModalFormula α), TwoProof φ → ⊨ φ := by
  intro φ h
  induction h
  case classical p h_cpl =>
    dsimp [dual_valid]
    intro f val w
    let m : DualModel α := DualModel.mk f val
    have hΓ : ∀ A, A ∈ (0 : Multiset (ModalFormula α)) → world_sat m w A := by
      intro A hA
      simp at hA
    have hvalid := cplSeqProof_sound (α := α) h_cpl m w hΓ
    rcases hvalid with ⟨B, hBmem, hBsat⟩
    have hEq : B = p := by
      simpa using hBmem
    rw [hEq] at hBsat
    exact hBsat
  case rl_re ψ₁ ψ₂ h ih =>
    dsimp [ModalRules.rl_re] at *
    dsimp [dual_valid] at *
    intro f val w
    let m : DualModel α := DualModel.mk f val
    have hiff : ∀ v, world_sat m v ψ₁ ↔ world_sat m v ψ₂ := by
      intro v
      have := ih f val v
      simpa [m] using (world_sat_iff).1 this
    have : world_sat m w (□ψ₁ ↔ □ψ₂) := by
      rw [world_sat_iff]
      cases w with
      | inl wn =>
        apply Iff.intro
        · intro h
          dsimp [DualModel.world_sat] at h
          dsimp [DualModel.world_sat]
          intro v hv
          exact (hiff v).mp (h v hv)
        · intro h
          dsimp [DualModel.world_sat] at h
          dsimp [DualModel.world_sat]
          intro v hv
          exact (hiff v).mpr (h v hv)
      | inr wp =>
        apply Iff.intro
        · intro h
          dsimp [DualModel.world_sat] at h
          dsimp [DualModel.world_sat]
          rcases h with ⟨v, hvrel, hsat⟩
          apply Exists.intro v
          apply And.intro hvrel
          exact (hiff v).mp hsat
        · intro h
          dsimp [DualModel.world_sat] at h
          dsimp [DualModel.world_sat]
          rcases h with ⟨v, hvrel, hsat⟩
          apply Exists.intro v
          apply And.intro hvrel
          exact (hiff v).mpr hsat
    simpa [m] using this

  case ax_def_dia p =>
    -- Need to prove: ⊨ (◇p ↔ ¬□¬p)
    -- That is: ∀ f val w, world_sat ⟨f, val⟩ w (◇p ↔ ¬□¬p)
    intro f val w
    let m : DualModel α := DualModel.mk f val
    -- First unfold the axiom definition
    dsimp [ModalAxioms.ax_def_dia]
    -- Use the biconditional theorem
    rw [world_sat_iff]
    constructor
    · -- Forward direction: ◇p → ¬□¬p
      intro h_dia
      rw [world_sat_neg]
      intro h_box_neg
      -- h_dia : world_sat m w (◇p)
      -- h_box_neg : world_sat m w (□¬p)
      -- Need to derive contradiction
      cases w with
      | inl wn =>
        -- w is a negative world
        dsimp [world_sat] at h_dia h_box_neg
        -- h_dia : ∃ v, m.frame.rel (.inl wn) v ∧ world_sat m v p
        -- h_box_neg : ∀ v, m.frame.rel (.inl wn) v → world_sat m v (¬p)
        rcases h_dia with ⟨v, hvrel, hsat_p⟩
        have h_neg_p := h_box_neg v hvrel
        rw [world_sat_neg] at h_neg_p
        exact h_neg_p hsat_p
      | inr wp =>
        -- w is a positive world
        dsimp [world_sat] at h_dia h_box_neg
        -- h_dia : ∀ v, m.frame.rel (.inr wp) v → world_sat m v p
        -- h_box_neg : ∃ v, m.frame.rel (.inr wp) v ∧ world_sat m v (¬p)
        rcases h_box_neg with ⟨v, hvrel, hsat_neg_p⟩
        have h_p := h_dia v hvrel
        rw [world_sat_neg] at hsat_neg_p
        exact hsat_neg_p h_p
    · -- Backward direction: ¬□¬p → ◇p
      intro h_neg_box
      rw [world_sat_neg] at h_neg_box
      -- h_neg_box : ¬world_sat m w (□¬p)
      cases w with
      | inl wn =>
        -- w is a negative world
        dsimp [world_sat] at h_neg_box ⊢
        -- Need to show: ∃ v, m.frame.rel (.inl wn) v ∧ world_sat m v p
        -- h_neg_box : ¬(∀ v, m.frame.rel (.inl wn) v → world_sat m v (¬p))
        -- Use classical logic to get the existential
        have h_exists : ∃ v, m.frame.rel (.inl wn) v ∧ ¬world_sat m v (¬p) := by
          cases Classical.em (∃ v, m.frame.rel (.inl wn) v ∧ ¬world_sat m v (¬p)) with
          | inl h => exact h
          | inr h_not =>
            exfalso
            apply h_neg_box
            intro v hvrel
            cases Classical.em (world_sat m v (¬p)) with
            | inl h_neg_p => exact h_neg_p
            | inr h_not_neg_p =>
              exfalso
              apply h_not
              exists v
        rcases h_exists with ⟨v, hvrel, h_not_neg_p⟩
        exists v
        constructor
        · exact hvrel
        · have h_double_neg : ¬¬world_sat m v p := h_not_neg_p
          cases Classical.em (world_sat m v p) with
          | inl h_p => exact h_p
          | inr h_not_p => exfalso; exact h_double_neg h_not_p
      | inr wp =>
        -- w is a positive world
        dsimp [world_sat] at h_neg_box ⊢
        -- Need to show: ∀ v, m.frame.rel (.inr wp) v → world_sat m v p
        -- h_neg_box : ¬(∃ v, m.frame.rel (.inr wp) v ∧ world_sat m v (¬p))
        intro v hvrel
        cases Classical.em (world_sat m v p) with
        | inl h_p => exact h_p
        | inr h_not_p =>
          exfalso
          apply h_neg_box
          apply Exists.intro v
          constructor
          · exact hvrel
          · rw [world_sat_neg]
            exact h_not_p
  case ax_kn2 p q =>
    -- Need to prove: ⊨ (((□(p → q) → (□p → □q)) ∧ □⊤) ∨ ((◇(p → q) → (◇p → ◇q)) ∧ ◇⊤))
    intro f val w
    let m : DualModel α := DualModel.mk f val
    -- Unfold the axiom definition
    unfold ModalAxioms.ax_KN2 ModalAxioms.ax_K_b ModalAxioms.ax_K
           ModalAxioms.ax_N_b ModalAxioms.ax_N ModalAxioms.ax_K_d ModalAxioms.ax_N_d
    -- Use the disjunction theorem
    rw [world_sat_or]
    -- The proof strategy depends on the world type
    cases w with
    | inl wn =>
      -- w is a negative world
      -- In negative worlds, □ behaves like universal quantification
      -- and ◇ behaves like existential quantification
      -- So the left disjunct (K_b ∧ N_b) should be true
      left
      rw [world_sat_and]
      constructor
      · -- Prove □(p → q) → (□p → □q) in negative world
        dsimp [world_sat]
        intro h_box_impl h_box_p v hvrel
        -- h_box_impl : ∀ v, m.frame.rel (.inl wn) v → world_sat m v (p → q)
        -- h_box_p : ∀ v, m.frame.rel (.inl wn) v → world_sat m v p
        -- Need to show: world_sat m v q
        have h_impl := h_box_impl v hvrel
        have h_p := h_box_p v hvrel
        exact h_impl h_p
      · -- Prove □⊤ in negative world
        dsimp [world_sat]
        intro v hvrel
        -- Need to show: world_sat m v ⊤
        exact world_sat_top
    | inr wp =>
      -- w is a positive world
      -- In positive worlds, □ behaves like existential quantification
      -- and ◇ behaves like universal quantification
      -- So the right disjunct (K_d ∧ N_d) should be true
      right
      rw [world_sat_and]
      constructor
      · -- Prove ◇(p → q) → (◇p → ◇q) in positive world
        dsimp [world_sat]
        intro h_dia_impl h_dia_p v hvrel
        -- h_dia_impl : ∀ v, m.frame.rel (.inr wp) v → world_sat m v (p → q)
        -- h_dia_p : ∀ v, m.frame.rel (.inr wp) v → world_sat m v p
        -- Need to show: world_sat m v q
        have h_impl := h_dia_impl v hvrel
        have h_p := h_dia_p v hvrel
        exact h_impl h_p
      · -- Prove ◇⊤ in positive world
        dsimp [world_sat]
        intro v hvrel
        -- Need to show: world_sat m v ⊤
        exact world_sat_top


theorem logic_2_complete :
    ∀ (φ : ModalFormula α), ⊨ φ → TwoProof φ := by
  sorry
