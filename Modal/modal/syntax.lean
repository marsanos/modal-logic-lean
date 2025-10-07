/- We take both box and diamond as primitive. Later, we add axioms
relating the two. We could have taken only box as primitive, and defined
diamond as the usual `◇A := ¬□¬A`. But it is common in textbooks to make
it this way. There are some weird modal logics in which the equivalence
does not hold, and that may be a reason to keep both as primitive.
Also, this is more symmetric, which is important for the use I make
of them in my dual Kripke models. -/

import Modal.cpl.syntax

class ModalSyntax (φ : Type) extends CPLSyntax φ where
  box : φ → φ
  dia : φ → φ

namespace ModalSyntax

prefix:40 "□" => box
prefix:40 "◇" => dia
-- same precedence as negation, larger than other Boolean connectives'
-- both taken as primitive

end ModalSyntax
