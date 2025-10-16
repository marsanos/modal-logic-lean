/- I use 𝓕 (backslash MCF) for the type of formulas...
or whatever is amenable to be used in its stead. -/

import Modal.common.syntax

namespace CPL

class Syntax (𝓕 : Type) where
  impl : 𝓕 → 𝓕 → 𝓕
  bot : 𝓕

namespace Syntax

def neg {𝓕 : Type} [Syntax 𝓕] (p : 𝓕)   : 𝓕 := impl p bot
def top {𝓕 : Type} [Syntax 𝓕]           : 𝓕 := neg bot
def or  {𝓕 : Type} [Syntax 𝓕] (p q : 𝓕) : 𝓕 := impl (neg p) q
def and {𝓕 : Type} [Syntax 𝓕] (p q : 𝓕) : 𝓕 := neg (impl p (neg q))
def iff {𝓕 : Type} [Syntax 𝓕] (p q : 𝓕) : 𝓕 := and (impl p q) (impl q p)


notation  "⊤"   => top
prefix:40 "¬"   => neg
infixr:35 " ∧ " => and
infixr:30 " ∨ " => or
infixr:20 " → " => impl
infixl:20 " ↔ " => iff
-- precedence levels: higher binds tighter
-- 40 (¬), 35 (∧), 30 (∨), 20 (→, ↔)

instance {𝓕 : Type} [Syntax 𝓕] : Common.Syntax.HasBot 𝓕 where bot := Syntax.bot

class HasImpl (𝓕 : Type) where
  impl : 𝓕 → 𝓕 → 𝓕

class HasBox (𝓕 : Type) where
  box : 𝓕 → 𝓕

end Syntax

end CPL
