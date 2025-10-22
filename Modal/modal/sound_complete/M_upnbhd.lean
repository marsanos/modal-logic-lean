import Modal.modal.models.nbhd
import Modal.modal.proof_systems.E_proof


namespace Modal.SoundComplete.M_UpNbhd

open Modal.ProofSystems Modal.Models


def is_upclosed : Nbhd.Frame → Prop :=
  fun f => ∀ w (X Y : Set f.world), X ∈ f.nbhd w → X ⊆ Y → Y ∈ f.nbhd w

theorem is_sound_strong (Atom : Type) :
    Logic.is_sound_strong (E.proof_system Atom) (@Nbhd.semantics Atom is_upclosed) :=
  by admit

theorem is_complete_weak (Atom : Type) :
    Logic.is_complete_weak (E.proof_system Atom) (@Nbhd.semantics Atom is_upclosed) :=
  by admit
-- M is not strongly complete wrt upclosed neighbourhood models

end Modal.SoundComplete.M_UpNbhd
