/- At the moment, I do not care how entailment is defined
for CPL. I only assume there is some definition for it
that satisfies the needed metatheorems. -/

import Modal.cpl.formula
import Modal.common.entailment
import Modal.common.modeling

namespace CPL
open Formula

variable {𝓐 : Type}

def models : Set (Formula 𝓐) → Formula 𝓐 → Prop := by admit
instance : HasModels (Formula 𝓐) where models := models

end CPL
