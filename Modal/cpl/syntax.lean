/- The type φ here represents formulas in a logic. Or, indeed, anything
for which we want to define the given operators. -/

class CPLSyntax (φ : Type) where
  impl : φ → φ → φ
  bot : φ

namespace CPLSyntax

def neg {φ : Type} [CPLSyntax φ] (p : φ)   : φ := impl p bot
def top {φ : Type} [CPLSyntax φ]           : φ := neg bot
def or  {φ : Type} [CPLSyntax φ] (p q : φ) : φ := impl (neg p) q
def and {φ : Type} [CPLSyntax φ] (p q : φ) : φ := neg (impl p (neg q))
def iff {φ : Type} [CPLSyntax φ] (p q : φ) : φ := and (impl p q) (impl q p)


notation  "⊥"   => bot
notation  "⊤"   => top
prefix:40 "¬"   => neg
infixr:35 " ∧ " => and
infixr:30 " ∨ " => or
infixr:20 " → " => impl
infixl:20 " ↔ " => iff
-- precedence levels: higher binds tighter
-- 40 (¬), 35 (∧), 30 (∨), 20 (→, ↔)

end CPLSyntax
