import Modal.modal.models.nbhd
import Modal.modal.proof_systems.E_proof


namespace Modal.SoundComplete.E_Nbhd

open Modal.ProofSystems Modal.Models


def all_frames : Nbhd.Frame → Prop := fun _ => True

theorem is_sound (Atom : Type) :
    Logic.is_sound (E.proof_system Atom) (@Nbhd.semantics Atom all_frames) (by rfl) :=
  by admit

theorem is_complete (Atom : Type) :
    Logic.is_complete (E.proof_system Atom) (@Nbhd.semantics Atom all_frames) (by rfl) :=
  by admit

end Modal.SoundComplete.E_Nbhd
