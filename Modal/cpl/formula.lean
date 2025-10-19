/- So, why do we have a syntax definition and a formula definition?
We could have several kinds of atoms, for instance,
producing different kinds of formulas. When we get to modal logic,
we may be interested in the product of two modal logics, and we will
need different actual syntax for each. -/

import Mathlib.Data.Nat.Basic
import Modal.cpl.syntax

namespace CPL

/- Here `Atom` is a type to identify atomic propositions (or atoms,
or propositional variables). Standard choices are strings and natural numbers,
but it also allows the use of uncountable types (e.g. real numbers) as atoms.
TODO: I could use `String` or `Nat` as the atomic type and avoid repeating
      the Atom type so much in so many definitions and results. -/

inductive Formula (Atom : Type := ℕ) where
  | atom : Atom → Formula Atom
  | bot  : Formula Atom
  | impl : Formula Atom → Formula Atom → Formula Atom
deriving DecidableEq

instance (Atom : Type) : Syntax (Formula Atom) where
  bot  := Formula.bot
  impl := Formula.impl

end CPL
