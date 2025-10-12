import Modal.cpl.proof
import Modal.cpl.syntax

open CPLSeq

namespace CPLTheorems

variable {Form : Type} [CPLSyntax Form]

theorem modus_ponens_prov {A B : Form} (hA : CPLProof A) (hAB : CPLProof (A → B)) : CPLProof B := by
  have h1 : CPLSeqProof (∅ ⊢ A) := hA
  have h2 : CPLSeqProof (∅ ⊢ (A → B)) := hAB
  have h3 : CPLSeqProof ((A → B) ::ₘ ∅ ⊢ B) := by
    apply CPLSeqProof.impl_l
    · exact h1
    · exact CPLSeqProof.identity
  exact CPLSeqProof.cut h2 h3

theorem absurd_prov {A : Form} (hA : CPLProof A) (hNA : CPLProof (¬A)) : CPLProof (⊥ : Form) := by
  have h1 : CPLSeqProof (∅ ⊢ A) := hA
  have h2 : CPLSeqProof (∅ ⊢ (¬A)) := hNA
  have h3 : CPLSeqProof ((¬A) ::ₘ ∅ ⊢ ⊥) := CPLSeqProof.neg_l h1
  exact CPLSeqProof.cut h2 h3

end CPLTheorems
