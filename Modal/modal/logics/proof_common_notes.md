# Notes: proof_common refactor

Date: 2025-10-15

This file records the discussion and the lightweight design used/proposed for refactoring the per-logic inductive proof types (EProof, KProof, MProof) into a single reusable abstraction, plus the parametric soundness theorem and a plan/contract for completeness. It also contains a verbatim copy of the current `proof_common.lean` file so you can recover the exact code.


## Summary of the idea

The three proof types `EProof`, `KProof`, and `MProof` shared the same constructors:

To avoid duplication, we introduced a small abstraction:

  - `has_axiom : Formula 𝓐 → Prop` — which formulas count as axioms for this logic
  - `has_rule  : InferenceRule (Formula 𝓐) → Prop` — which inference rules the logic supports

  - `assumption` — `p ∈ Γ`
  - `cpl` — CPL-derived tautologies
  - `ax` — `L.has_axiom φ`
  - `apply_rule` — `L.has_rule R` and a proof of the premise


This reduces duplicated inductives and centralizes the structural induction used in meta-theory proofs.


## Parametric soundness theorem

Because soundness is local to constructors, we added a modular theorem:

`LogicProof.sound` takes:
  1. CPL preservation: `∀ φ, CPL.entails ∅ (to_cpl φ) → valid φ`
  2. Axiom validity: `∀ φ, L.has_axiom φ → valid φ`
  3. Rule preservation: `∀ R, L.has_rule R → (valid R.premise → valid R.conclusion)`

and proves: for all Γ, φ, if all formulas in Γ are `valid` and `LogicProof L Γ φ` then `valid φ`.

This is a single structural induction, so proving soundness for a concrete logic (e.g. K) reduces to proving the three small lemmas above for the specific `valid` predicate (e.g. `Kripke.valid`). This is typically straightforward and already present in the per-logic `sound_complete` files.


## Completeness — why it's trickier

Completeness requires a canonical model construction and a global truth lemma. That depends on the logic in ways that are not local to constructors:

Thus a single "one-line" completeness theorem for every logic is not realistic without asking each logic to supply the canonical-model ingredients.

### Minimal contract for a generic completeness scaffold

If you want a reusable completeness scaffolding, aim for a `CompletenessSpec` that supplies:

1. A Lindenbaum / maximal consistent extension lemma:
   - `Consistent Γ → ∃ M, Γ ⊆ M ∧ MaxConsistent M ∧ (closure properties)`

2. Canonical model ingredients (definitions):
   - worlds := maximal consistent sets
   - canonical frame relation / neighbourhood function defined from syntactic conditions

3. Truth lemma:
   - `∀ M, ∀ φ, φ ∈ M ↔ world_sat canonical_model M φ`.

4. Frame/property lemma:
   - The canonical frame satisfies the target frame/class property (e.g. `IsKripkeFrame`, `IsUpwardClosed`, ...).

5. The final completeness step:
   - If `φ` is not provable, `{¬φ}` is consistent → extend to `M` → by truth lemma M ⊭ φ → extract countermodel.

A top-level `Completeness.from_spec` lemma can be written once: given a `CompletenessSpec` instance, derive completeness for the entailment system induced by `LogicProof L` and the model class in the spec. Each logic then only provides the spec instance (which still contains the non-trivial canonical-model proofs).

### Practical choices



## How to use the soundness theorem (example)

For logic K and Kripke models, you would:
  - `cpl_valid : ∀ φ, (CPL.Entailment _).entails ∅ (to_cpl φ) → Kripke.valid φ`
  - `ax_k_valid : ∀ φ, L_K.has_axiom φ → Kripke.valid φ` (i.e. each instance of `Axioms.k` is valid)
  - `rl_re_valid` / `rl_nec_valid` : each rule preserves Kripke.valid

This pattern is already what per-logic `sound_complete` files do; `LogicProof.sound` centralizes it.


## Verbatim copy of the current `proof_common.lean`

Below is an exact copy of the `Modal/modal/logics/proof_common.lean` file as it stood when these notes were created. Keep it here so you can restore or revisit the code later.

```lean
import Modal.cpl.cpl
import Modal.modal.common.formula
import Modal.modal.common.axioms_rules


open Modal

variable {𝓐 : Type}

/-
A small generic abstraction to avoid repeating the same inductive proof
constructors for each modal logic. The idea: provide a LogicSpec which
exposes which formulas are accepted as axioms and which inference rules
are available. The generic `LogicProof` inductive uses those predicates to
provide `ax` and `apply_rule` constructors. Specific logics (E, K, M)
become just instances of `LogicSpec` and short type aliases.
/-

structure LogicSpec where
  has_axiom : Formula 𝓐 → Prop
  has_rule  : InferenceRule (Formula 𝓐) → Prop

inductive LogicProof (L : LogicSpec) : Set (Formula 𝓐) → Formula 𝓐 → Prop where
  | assumption {Γ : Set (Formula 𝓐)} {p : Formula 𝓐}
      (h : p ∈ Γ) :
      LogicProof L Γ p
  | cpl {Γ : Set (Formula 𝓐)} {φ : Formula 𝓐}
      (h_cpl : (CPL.Entailment (Formula 𝓐)).entails ∅ ((to_cpl 𝓐) φ)) :
      LogicProof L Γ φ
  | ax {Γ : Set (Formula 𝓐)} {φ : Formula 𝓐}
      (h : L.has_axiom φ) :
      LogicProof L Γ φ
  | apply_rule {Γ : Set (Formula 𝓐)} {R : InferenceRule (Formula 𝓐)}
      (hR : L.has_rule R) (h_prem : LogicProof L Γ R.premise) :
      LogicProof L Γ R.conclusion

/-- Example LogicSpec instances for the logics you had (E, K, M).
    These show how to express axiom schemata and which rules are
    available. You can adjust the predicates if you want a different
    notion (e.g. allow additional schemas or parametrised schemas).
def L_E : LogicSpec :=
  { has_axiom := fun _ => False
  , has_rule  := fun R => R = Rules.re }

def L_K : LogicSpec :=
  { has_axiom := fun φ => ∃ (φ1 ψ1 : Formula 𝓐), φ = Axioms.k φ1 ψ1
  , has_rule  := fun R => R = Rules.re ∨ R = Rules.nec }

def L_M : LogicSpec :=
  { has_axiom := fun φ => ∃ (φ1 ψ1 : Formula 𝓐), φ = Axioms.m φ1 ψ1
  , has_rule  := fun R => R = Rules.re ∨ R = Rules.nec }

/- Type aliases to recover the old names easily. -/
abbrev EProof := LogicProof L_E
abbrev KProof := LogicProof L_K
abbrev MProof := LogicProof L_M

/- Parametric soundness theorem

theorem LogicProof.sound
  (L : LogicSpec)
  {valid : Formula 𝓐 → Prop}
  (h_cpl : ∀ φ, (CPL.Entailment (Formula 𝓐)).entails ∅ ((to_cpl 𝓐) φ) → valid φ)
  (h_ax  : ∀ φ, L.has_axiom φ → valid φ)
  (h_rule : ∀ R, L.has_rule R → (valid R.premise → valid R.conclusion)) :
  ∀ (Γ : Set (Formula 𝓐)) (φ : Formula 𝓐), (∀ ψ, ψ ∈ Γ → valid ψ) → LogicProof L Γ φ → valid φ := by
  intro Γ φ hΓ
  intro hp
  induction hp with
  | assumption _ _ h => exact hΓ _ h
  | cpl _ _ h => exact h_cpl _ h
  | ax _ _ h => exact h_ax _ h
  | apply_rule _ _ _ hR h_prem ih => exact h_rule _ hR (ih hΓ)

/-
You can instantiate `LogicProof.sound` with the appropriate `valid`
predicate for your model class (e.g. `Kripke.valid`, `Dual.valid`,
`Neighborhood.valid`) and supply the three hypotheses:
  * CPL-tautologies are valid (for the `cpl` constructor)
  * every axiom instance of `L` is valid
  * every inference rule in `L` preserves validity

This makes soundness proofs modular: you only need to prove the last
two bullet points for each logic (these are typically small lemmas in
your existing `sound_complete` files), and then `LogicProof.sound` gives
the full soundness result for free.
```


If you'd like, I can also:

Tell me if you'd rather the notes be placed somewhere else or formatted differently.