/- So, why do we have a syntax definition and a formula definition?
It... seems right. We could have several kinds of atoms, for instance,
producing different kinds of formulas. When we get to modal logic,
we may be interested in the product of two modal logics, and we will
need different actual syntax for each.
Also, in the definition of a logic system we need a type (not a class). -/


import Modal.cpl.syntax
import Modal.common.entailment

namespace CPL

/- Here 𝓐 (backslash MCA) is a type to identify atomic propositions (or atoms,
or propositional variables). Standard choices are strings and natural numbers,
but it also allows the use of uncountable types (e.g. real numbers) as atoms. -/

inductive Formula (𝓐 : Type) where
  | atom : 𝓐 → Formula 𝓐
  | bot  : Formula 𝓐
  | impl : Formula 𝓐 → Formula 𝓐 → Formula 𝓐
deriving DecidableEq

instance (𝓐 : Type) : Syntax (Formula 𝓐) where
  bot  := Formula.bot
  impl := Formula.impl

instance (𝓐 : Type) : HasBot (Formula 𝓐) where
  bot := ⊥

instance (𝓐 : Type) : HasNeg (Formula 𝓐) where
  neg := fun φ => ¬ φ

end CPL
