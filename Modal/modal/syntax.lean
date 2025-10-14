/- We take box as primitive and define diamond as the usual `◇ = ¬□¬`.
While some textbooks take both as primitive, defining diamond simplifies
structural inductions and proofs. The symmetry in dual models is
maintained through the semantics. -/

import Modal.cpl.syntax

namespace Modal

class Syntax (φ : Type) extends CPL.Syntax φ where
  box : φ → φ

namespace Syntax

def dia {φ : Type} [Syntax φ] (p : φ) : φ := ¬ box (¬p)

prefix:40 "□" => box
prefix:40 "◇" => dia
-- same precedence as negation, larger than other Boolean connectives'

end Syntax

end Modal
