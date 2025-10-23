import Modal.modal.models.nbhd
import Modal.modal.proof_systems.EM_proof


namespace Modal.SoundComplete.EM_UpNbhd

open Modal.ProofSystems Modal.Models.Nbhd

def upward_closed (f : Frame) : Prop :=
  ∀ w : f.world, ∀ X Y : Set f.world, X ∈ f.nbhd w → X ⊆ Y → Y ∈ f.nbhd w

def upward_closed_semantics {Atom : Type} : Logic.Semantics (Formula Atom) :=
  { model := { m : Model Atom // upward_closed m.frame },
    satisfies := fun m φ => model_sat m.val φ }

theorem is_sound_strong (Atom : Type) :
    Logic.is_sound_strong (EM.proof_system Atom) upward_closed_semantics :=
  by admit

theorem is_complete_weak (Atom : Type) :
    Logic.is_complete_weak (EM.proof_system Atom) upward_closed_semantics :=
  by admit
-- M is not strongly complete wrt upclosed neighbourhood models

end Modal.SoundComplete.EM_UpNbhd
