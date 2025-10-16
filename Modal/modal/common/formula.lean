/- We define the syntax and the formulas separately.
This would be especially useful if we intend to work with products of logics
later on, in which each logic would need to use different actual modal
operators.

𝓐 (backslash MCA) represents the type of atoms (= atomic propositions
= propositional variables). Typically, 𝓐 = ℕ or 𝓐 = String, but also
uncountable types are possible, e.g. 𝓐 = ℝ. -/


import Modal.modal.common.syntax
import Modal.common.syntax
import Modal.cpl.syntax
import Modal.cpl.formula
import Modal.common.entailment

namespace Modal

inductive Formula (𝓐 : Type) where
  | atom : 𝓐 → Formula 𝓐
  | bot  : Formula 𝓐
  | impl : Formula 𝓐 → Formula 𝓐 → Formula 𝓐
  | box  : Formula 𝓐 → Formula 𝓐
deriving DecidableEq

instance (𝓐 : Type) : Syntax (Formula 𝓐) where
  bot  := Formula.bot
  impl := Formula.impl
  box  := Formula.box

instance (𝓐 : Type) : Common.Syntax.HasBot (Formula 𝓐) where
  bot := ⊥

instance (𝓐 : Type) : CPL.Syntax.HasImpl (Formula 𝓐) where
  impl := Formula.impl

instance (𝓐 : Type) : Modal.Syntax.HasBox (Formula 𝓐) where
  box := Formula.box

end Modal

/- The type of the function `to_cpl` allows for any modal formula
to be an atom in the resulting CPL formula. This would not be
appropriate. But the translation `to_cpl` only produces
formulas where the atoms are either actual atoms already in the original
modal formula, or boxed formulas (□φ). This is as it should be.

Also, while □φ is considered an atom, the equivalent ¬◇¬φ is not,
it is the negation of an atom. This is all OK. -/

variable (𝓐 : Type)

def to_cpl : Modal.Formula 𝓐 → CPL.Formula (Modal.Formula 𝓐)
  | Modal.Formula.atom α => CPL.Formula.atom (Modal.Formula.atom α)
  | Modal.Formula.bot => CPL.Formula.bot
  | Modal.Formula.impl φ ψ => CPL.Formula.impl (to_cpl φ) (to_cpl ψ)
  | Modal.Formula.box φ => CPL.Formula.atom (Modal.Formula.box φ)
