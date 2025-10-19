import Modal.modal.common.syntax
import Modal.common.logic
import Modal.cpl.syntax
import Modal.cpl.formula

namespace Modal

inductive Formula (Atom : Type) where
  | atom : Atom → Formula Atom
  | bot  : Formula Atom
  | impl : Formula Atom → Formula Atom → Formula Atom
  | box  : Formula Atom → Formula Atom
deriving DecidableEq

instance (Atom : Type) : Syntax (Formula Atom) where
  bot  := Formula.bot
  impl := Formula.impl
  box  := Formula.box
-- Given that Modal.Syntax extends CPL.Syntax,
-- this declaration internally implies that Formula Atom is
-- also an instance of CPL.Syntax.


/- The type of the function `to_cpl` allows for any modal formula
to be an atom in the resulting CPL formula. This would not be
appropriate. But the translation `to_cpl` only produces
formulas where the atoms are either actual atoms already in the original
modal formula, or boxed formulas (□φ). This is as it should be.

Also, while □φ is considered an atom, the equivalent ¬◇¬φ is not,
it is the negation of an atom. This is all OK. -/

def to_cpl {Atom : Type} : Modal.Formula Atom → CPL.Formula (Modal.Formula Atom)
  | Modal.Formula.atom α => CPL.Formula.atom (Modal.Formula.atom α)
  | Modal.Formula.bot => CPL.Formula.bot
  | Modal.Formula.impl φ ψ => CPL.Formula.impl (to_cpl φ) (to_cpl ψ)
  | Modal.Formula.box φ => CPL.Formula.atom (Modal.Formula.box φ)

end Modal
