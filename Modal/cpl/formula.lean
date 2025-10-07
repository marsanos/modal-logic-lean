/- So, why do we have a syntax definition and a formula definition?
It... seems right to me. We could have several kinds of atoms, for instance,
producing different kinds of formulas. When we get to modal logic,
we may be interested in the product of two modal logics, and we will
need different actual syntax for each. -/


import Modal.cpl.syntax

namespace CPLFormula

-- Here α is a type to identify atomic propositions. Standard choices
-- are strings and natural numbers, but it also allows the use of uncountable
-- types (e.g. real numbers) as atoms.

inductive CPLFormula (α : Type) where
  | atom : α → CPLFormula α
  | bot  : CPLFormula α
  | impl : CPLFormula α → CPLFormula α → CPLFormula α
deriving DecidableEq

instance (α : Type) : CPLSyntax (CPLFormula α) where
  bot  := CPLFormula.bot
  impl := CPLFormula.impl

end CPLFormula
