import Modal.modal.models.kripke
import Modal.modal.proof_systems.K_proof


namespace Modal.SoundComplete.K_Kripke

open Modal.ProofSystems Modal.Models


def all_frames : Kripke.Frame → Prop := fun _ => True

theorem is_sound (Atom : Type) :
    Logic.is_sound (K.proof_system Atom) (@Kripke.semantics Atom all_frames) (by rfl) :=
  by admit

theorem is_complete (Atom : Type) :
     Logic.is_complete (K.proof_system Atom) (@Kripke.semantics Atom all_frames) (by rfl) :=
  by admit

end Modal.SoundComplete.K_Kripke
