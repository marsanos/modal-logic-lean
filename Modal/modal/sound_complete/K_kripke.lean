import Modal.modal.models.kripke
import Modal.modal.proof_systems.K_proof


namespace Modal.SoundComplete.K_Kripke

open Modal.ProofSystems Modal.Models


def all_frames : Kripke.Frame → Prop := fun _ => True

theorem is_sound_strong (Atom : Type) :
    Logic.is_sound_strong (K.proof_system Atom) Kripke.semantics :=
  by admit

theorem is_complete_strong (Atom : Type) :
     Logic.is_complete_strong (K.proof_system Atom) Kripke.semantics :=
  by admit
-- See, for example, Blackburn et al., Example 4.11 and Proposition 4.12.

end Modal.SoundComplete.K_Kripke
