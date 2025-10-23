- study about strong completeness where only weak one is asserted

- review how I'm dealing with conditions on frames

- make it possible logic+rules+axioms to build a new logic
  - in the same way as frame+condition creates new semantics

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

- review the completeness proof:
"""
Analysis of Each admit-marked Lemma:

deriv_iff_mem_mcs - ✅ SAFE
Depends only on: The proof system EM
Independent of: Semantics/models
Reason: This is a purely syntactic characterization of derivability

mcs_no_bot - ✅ SAFE
Depends only on: Definition of MCS (consistent + maximal)
Independent of: Which logic, which semantics
Reason: Definitional - any MCS is consistent, so ⊥ can't be in it

mcs_impl_closed - ✅ SAFE
Depends only on: The proof system EM having modus ponens
Independent of: Semantics/models
Reason: If proof system proves φ → ψ and φ, it proves ψ (standard for Hilbert systems)

mcs_box_of_all - ⚠️ REQUIRES VERIFICATION
Depends on: The proof system EM having certain necessitation/normality properties
The key question: Does EM have the rule that allows deriving □¬φ from Γ ⊢ ¬φ when Γ contains only boxed formulas?
This is specific to normal modal logics but EM is indeed normal (has axiom K or equivalent)

mcs_box_of_exists_p - ⚠️ REQUIRES VERIFICATION
This is the dual of #4
Depends on: Same normality properties of EM
For dual semantics specifically: The proof works because EM logic is the same for both n-worlds and p-worlds (it's symmetric)

existence_pworld - ⚠️ REQUIRES VERIFICATION
This witness construction works if the set {ψ | ◇ψ ∈ Γ} ∪ {φ} is consistent when □φ ∈ Γ
Depends on: Properties of EM (specifically the diamond/box interaction)
For dual semantics: This is where your invention might matter
"""
