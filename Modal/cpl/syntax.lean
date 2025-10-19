/- I use 𝓕 (backslash MCF) for the type of formulas...
or whatever is amenable to be used in its stead. -/


namespace CPL

class Syntax (Form : Type) where
  impl : Form → Form → Form
  bot : Form

namespace Syntax

def neg {Form : Type} [Syntax Form] (p : Form)   : Form := impl p bot
def top {Form : Type} [Syntax Form]           : Form := neg bot
def or  {Form : Type} [Syntax Form] (p q : Form) : Form := impl (neg p) q
def and {Form : Type} [Syntax Form] (p q : Form) : Form := neg (impl p (neg q))
def iff {Form : Type} [Syntax Form] (p q : Form) : Form := and (impl p q) (impl q p)

notation  "⊥"   => bot
notation  "⊤"   => top
prefix:40 "¬"   => neg
infixr:35 " ∧ " => and
infixr:30 " ∨ " => or
infixr:20 " → " => impl
infixl:20 " ↔ " => iff
-- precedence levels: higher binds tighter
-- 40 (¬), 35 (∧), 30 (∨), 20 (→, ↔)

end Syntax

end CPL
