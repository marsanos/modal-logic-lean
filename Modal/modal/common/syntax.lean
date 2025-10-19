/- We take box as primitive and define diamond as the usual `◇ = ¬□¬`.
While some textbooks take both as primitive, defining diamond simplifies
structural inductions and proofs. The symmetry in dual models is
maintained through the semantics. -/

import Modal.cpl.syntax

namespace Modal

class Syntax (Form : Type) extends CPL.Syntax Form where
  box : Form → Form

namespace Syntax

def dia {Form : Type} [Syntax Form] (φ : Form) : Form := ¬ box (¬φ)

prefix:40 "□" => box
prefix:40 "◇" => dia
-- same precedence as negation, larger than other Boolean connectives'

end Syntax

end Modal
