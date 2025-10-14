/- We define the syntax and the formulas separately.
This would be especially useful if we intend to work with products of logics
later on, in which each logic would need to use different actual modal
operators.

𝓐 (backslash MCA) represent the type of atoms (= atomic propositions
= propositional variables). Typically, 𝓐 = ℕ or 𝓐 = String, but also
uncountable types are possible, e.g. 𝓐 = ℝ. -/


import Modal.modal.syntax

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

end Modal
