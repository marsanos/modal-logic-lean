/- We take box as primitive and define diamond as the usual `◇ = ¬□¬`.
While some textbooks take both as primitive, defining diamond simplifies
structural inductions and proofs. The symmetry in dual Kripke models is
maintained through the semantics. -/

import Modal.cpl.syntax

class ModalSyntax (φ : Type) extends CPLSyntax φ where
  box : φ → φ

namespace ModalSyntax

prefix:40 "□" => box
-- same precedence as negation, larger than other Boolean connectives'

def dia {φ : Type} [ModalSyntax φ] (p : φ) : φ := ¬□¬p

prefix:40 "◇" => dia

end ModalSyntax
