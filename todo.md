- rename logic M to EM
- review how I'm dealing with conditions on frames
- make it possible logic+rules+axioms to build a new logic
  - in the same way as frame+condition creates new semantics
- check in books about the non strong completeness of K, E M
- avoid the `Atom` annoyance:
    ```lean
    variable {Atom : Type}

    -- Type aliases for the section
    local abbrev MFormula := Modal.Formula Atom
    local abbrev DModel := Dual.Model Atom  
    local abbrev DFrame := Dual.Frame
    local abbrev MProofSystem := M.proof_system Atom

    lemma rl_re_is_valid (φ ψ : MFormula) (model : DModel) :
        Dual.model_sat model (Rules.re φ ψ).premise →
        Dual.model_sat model (Rules.re φ ψ).conclusion := by
    intro h w
    ...
    ```
