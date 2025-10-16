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

end CPL
