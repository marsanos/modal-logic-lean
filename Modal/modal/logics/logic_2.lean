import Modal.cpl.proof
import Modal.modal.formula
import Modal.modal.axioms_rules


open ModalAxioms ModalRules CPLSeq ModalFormula

variable {α : Type} [ModalSyntax α]

/-
  Derivability relation for Logic 2 (modal logic with KN2 axiom).

  The `classical` constructor uses CPL sequent calculus on modal formulas.
  Since CPLSeqProof only has rules for propositional connectives (∧, ∨, →, ¬, ⊥),
  modal formulas with □ or ◇ at the top level are treated as atomic propositions.
  This allows propositional reasoning among modal formulas without decomposing
  the modal operators themselves.

  Example: From hypotheses {□p, □p → q}, we can derive q using the classical
  constructor, even though □p is treated as an atomic formula by the CPL rules.
-/
inductive TwoDerivable (Γ : Multiset (ModalFormula α)) : ModalFormula α → Prop where
  | assumption {φ : ModalFormula α} (h : φ ∈ Γ) : TwoDerivable Γ φ
  | classical {φ : ModalFormula α} (h : CPLSeqProof (Γ ⊢ φ)) :
      TwoDerivable Γ φ
  | rl_re {φ ψ : ModalFormula α} (h : TwoDerivable Γ (rl_re φ ψ).premise) :
      TwoDerivable Γ (rl_re φ ψ).conclusion
  | ax_def_dia {φ : ModalFormula α} : TwoDerivable Γ (ax_def_dia φ)
  | ax_kn2 {φ ψ : ModalFormula α} : TwoDerivable Γ (ax_KN2 φ ψ)

notation:40 Γ " ⊢₂ " φ => TwoDerivable Γ φ

def TwoProof (φ : ModalFormula α) : Prop := ∅ ⊢₂ φ

def TwoConsistent (Γ : Multiset (ModalFormula α)) : Prop := ¬(Γ ⊢₂ ⊥)



/-
  Example: Classical propositional reasoning with modal formulas.

  This example shows that modal formulas with □ or ◇ at the top level are
  treated as atomic by the CPL sequent calculus. Here we derive
  □(p∨◇q) → □(p∨◇q), a tautology that holds for any formula □(p∨◇q).

  The CPL impl_r rule introduces the implication, and the identity rule treats
  □(p∨◇q) as an atomic formula that can be found on both sides. This
  demonstrates that the classical constructor enables propositional reasoning
  about modal formulas without decomposing the modal operators.
-/
example {p q : ModalFormula α} :
    TwoDerivable ∅ (□(p∨◇q) → □(p∨◇q)) := by
  apply TwoDerivable.classical
  -- Prove: ∅ ⊢ □(p∨◇q) → □(p∨◇q)
  apply CPLSeqProof.impl_r
  -- Prove: {□(p∨◇q)} ⊢ □(p∨◇q)
  apply CPLSeqProof.identity
  simp
