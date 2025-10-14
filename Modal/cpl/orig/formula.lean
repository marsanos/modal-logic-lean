/- So, why do we have a syntax definition and a formula definition?
It... seems right to me. We could have several kinds of atoms, for instance,
producing different kinds of formulas. When we get to modal logic,
we may be interested in the product of two modal logics, and we will
need different actual syntax for each. -/


import Modal.cpl.syntax

namespace CPLFormula

/- Here 𝓐 (backslash MCA) is a type to identify atomic propositions (or atoms,
or propositional variables). Standard choices are strings and natural numbers,
but it also allows the use of uncountable types (e.g. real numbers) as atoms. -/

inductive CPLFormula (𝓐 : Type) where
  | atom : 𝓐 → CPLFormula 𝓐
  | bot  : CPLFormula 𝓐
  | impl : CPLFormula 𝓐 → CPLFormula 𝓐 → CPLFormula 𝓐
deriving DecidableEq

instance (𝓐 : Type) : CPL.Syntax (CPLFormula 𝓐) where
  bot  := CPLFormula.bot
  impl := CPLFormula.impl

end CPLFormula
