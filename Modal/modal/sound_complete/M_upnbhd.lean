import Modal.modal.models.nbhd
import Modal.modal.proof_systems.E_proof


namespace Modal.SoundComplete.M_UpNbhd

open Modal.ProofSystems Modal.Models


def is_upclosed : Nbhd.Frame → Prop :=
  fun f => ∀ w (X Y : Set f.world), X ∈ f.nbhd w → X ⊆ Y → Y ∈ f.nbhd w

theorem is_sound (Atom : Type) :
    Logic.is_sound (E.proof_system Atom) (@Nbhd.semantics Atom is_upclosed) (by rfl) :=
  by admit

theorem is_complete (Atom : Type) :
    Logic.is_complete (E.proof_system Atom) (@Nbhd.semantics Atom is_upclosed) (by rfl) :=
  by admit

end Modal.SoundComplete.M_UpNbhd
