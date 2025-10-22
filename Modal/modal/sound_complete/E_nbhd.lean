import Modal.modal.models.nbhd
import Modal.modal.proof_systems.E_proof


namespace Modal.SoundComplete.E_Nbhd

open Modal.ProofSystems Modal.Models

theorem is_sound_strong (Atom : Type) :
    Logic.is_sound_strong (E.proof_system Atom) Nbhd.semantics :=
  by admit

theorem is_complete_weak (Atom : Type) :
    Logic.is_complete_weak (E.proof_system Atom) Nbhd.semantics :=
  by admit
-- E is not strongly complete wrt neighborhood models

end Modal.SoundComplete.E_Nbhd
