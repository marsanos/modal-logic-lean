import Modal.cpl.entailment
import Modal.cpl.modeling


namespace CPL

theorem sound {𝓐 : Type} {Γ : Set (Formula 𝓐)} {φ : Formula 𝓐}
        (h : CPL.entails Γ φ) : (CPL.models Γ φ) :=
    by admit


theorem complete {𝓐 : Type} {Γ : Set (Formula 𝓐)} {φ : Formula 𝓐}
        (h : CPL.models Γ φ) : (CPL.entails Γ φ) :=
    by admit

end CPL
