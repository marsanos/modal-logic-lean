import Modal.cpl.proof

namespace CPLTheorems

open CPLSeq


theorem mp {φ : Type} [CPLSyntax φ] {p q : φ}
    (h1 : CPLProof (p)) (h2 : CPLProof (p → q)) : CPLProof (q) := by
  unfold CPLProof at *
  have h_impl_l : CPLSeqProof ((p → q) ::ₘ ∅ ⊢ q) :=
    CPLSeqProof.impl_l h1 CPLSeqProof.identity
  exact CPLSeqProof.cut h2 h_impl_l


end CPLTheorems
