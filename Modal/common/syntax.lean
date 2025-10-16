namespace Common.Syntax

class HasBot (𝓕 : Type) where
  bot : 𝓕

notation "⊥" => HasBot.bot

end Common.Syntax
