/- At the moment, I do not care how entailment is defined
for CPL. I only assume there is some definition for it
that satisfies the needed metatheorems. -/

import Modal.cpl.formula
import Modal.common.entailment

namespace CPL
open Formula

def Entailment (𝓐 : Type) : EntailmentSystem :=
  { formula : Type := Formula 𝓐
    entails : Set (Formula 𝓐) → Formula 𝓐 → Prop := by admit }

instance (𝓐 : Type) : EntailmentSystem := Entailment 𝓐

end CPL
