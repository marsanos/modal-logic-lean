/- This defines a sequent calculus for CPL. It is of the kind
of sequent calculus with a single formula on the rhs.
We use a Multiset on the lhs, instead of a Finset, to allow
for possibly infinite sets... which we may never use.

Pattern matching on multisets is not very reliable. For example,
it seems that `A ::ₘ B ::ₘ Γ` does not match `B ::ₘ A ::ₘ Γ`.
This makes some rules difficult to use in proofs.
An alternative would be to use instead just `Γ` with the added
provisos `(ha: A ∈ Γ)` and `(hb: B ∈ Γ)`.

This axiomatization includes a `cut` rule, which is not really needed,
because this logic has cut elimination. It is OK for me by now. -/


import Mathlib.Data.Multiset.Basic
import Modal.cpl.syntax

namespace CPLSeq

structure Sequent (Form : Type) where
  left : Multiset Form
  right : Form

notation:40 Γ " ⊢ " A => Sequent.mk Γ A
notation "∅" => (Multiset.empty)

inductive CPLSeqProof {Form : Type} [CPLSyntax Form] :
    Sequent Form → Prop where
  | identity {Γ : Multiset Form} {A : Form} :
      CPLSeqProof (A ::ₘ Γ ⊢ A)

  | and_l {Γ : Multiset Form} {A B C : Form}
      (h : CPLSeqProof (A ::ₘ B ::ₘ Γ ⊢ C)) :
      CPLSeqProof ((A ∧ B) ::ₘ Γ ⊢ C)

  | and_r {Γ : Multiset Form} {A B : Form}
      (hA : CPLSeqProof (Γ ⊢ A)) (hB : CPLSeqProof (Γ ⊢ B)) :
      CPLSeqProof (Γ ⊢ (A ∧ B))

  | or_l {Γ : Multiset Form} {A B C : Form}
      (hA : CPLSeqProof (A ::ₘ Γ ⊢ C)) (hB : CPLSeqProof (B ::ₘ Γ ⊢ C)) :
      CPLSeqProof ((A ∨ B) ::ₘ Γ ⊢ C)

  | or_r1 {Γ : Multiset Form} {A B : Form}
      (h : CPLSeqProof (Γ ⊢ A)) :
      CPLSeqProof (Γ ⊢ (A ∨ B))

  | or_r2 {Γ : Multiset Form} {A B : Form}
      (h : CPLSeqProof (Γ ⊢ B)) :
      CPLSeqProof (Γ ⊢ (A ∨ B))

  | impl_l {Γ : Multiset Form} {A B C : Form}
      (hA : CPLSeqProof (Γ ⊢ A)) (hB : CPLSeqProof (B ::ₘ Γ ⊢ C)) :
      CPLSeqProof ((A → B) ::ₘ Γ ⊢ C)

  | impl_r {Γ : Multiset Form} {A B : Form}
      (h : CPLSeqProof (A ::ₘ Γ ⊢ B)) :
      CPLSeqProof (Γ ⊢ (A → B))

  | neg_l {Γ : Multiset Form} {A C : Form}
      (h : CPLSeqProof (Γ ⊢ A)) :
      CPLSeqProof ((¬A) ::ₘ Γ ⊢ C)

  | neg_r {Γ : Multiset Form} {A : Form}
      (h : CPLSeqProof (A ::ₘ Γ ⊢ ⊥)) :
      CPLSeqProof (Γ ⊢ (¬A))

  | cut {Γ : Multiset Form} {A B : Form}
      (hA : CPLSeqProof (Γ ⊢ A)) (hB : CPLSeqProof (A ::ₘ Γ ⊢ B)) :
      CPLSeqProof (Γ ⊢ B)

def CPLProof {Form : Type} [CPLSyntax Form] (A : Form) : Prop :=
  CPLSeqProof (∅ ⊢ A)

end CPLSeq
