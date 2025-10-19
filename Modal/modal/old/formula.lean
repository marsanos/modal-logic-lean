/- As in the classical case, we define the syntax and the formulas separately.
This would be especially useful if we intend to work with products of logics
later on, in which each logic would need to use different actual modal
operators. -/


import Modal.modal.syntax

namespace ModalFormula

inductive ModalFormula (α : Type) where
  | atom : α → ModalFormula α
  | bot  : ModalFormula α
  | impl : ModalFormula α → ModalFormula α → ModalFormula α
  | box  : ModalFormula α → ModalFormula α
deriving DecidableEq

instance (α : Type) : ModalSyntax (ModalFormula α) where
  bot  := ModalFormula.bot
  impl := ModalFormula.impl
  box  := ModalFormula.box

end ModalFormula
