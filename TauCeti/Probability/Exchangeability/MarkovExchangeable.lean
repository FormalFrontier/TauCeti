/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.TransitionCount
public import TauCeti.Probability.Exchangeability.Basic

/-!
# Markov exchangeability

A process `X : ℕ → Ω → α` on a countable state space is **Markov exchangeable** — Diaconis and
Freedman's *partial exchangeability* — when two finite paths that start at the same state and make
the same number of transitions from each state to each state are equally likely:

```text
u 0 = v 0  →  transitionCount u = transitionCount v  →  prefixLaw μ X (n + 1) {u} =
  prefixLaw μ X (n + 1) {v}
```

This is the symmetry that a Markov chain has and an exchangeable process has, and it is the
hypothesis of the Diaconis–Freedman representation theorem, which says that a recurrent Markov
exchangeable process is a mixture of Markov chains. This file sets up the notion and its two
sources.

Markov exchangeability is a genuine weakening of exchangeability. Exchangeability asks for
invariance under *all* rearrangements of a finite path, whereas Markov exchangeability asks for it
only between paths sharing a start and a transition-count matrix; the latter class of paths is
strictly smaller, because a rearrangement generally destroys the transition counts. That the
implication `Exchangeable → MarkovExchangeable` nevertheless holds is a conservation law for words:
the transition counts and the first letter already determine the occurrence counts, hence the
rearrangement class (`TauCeti.exists_perm_comp_of_transitionCount_eq`). That the implication is
strict is witnessed by the deterministic 3-cycle, in
`TauCeti/Probability/Exchangeability/ThreeCycle.lean`.

## Main definitions

* `TauCeti.Probability.MarkovExchangeable`: the symmetry above.

## Main results

* `TauCeti.Probability.Exchangeable.markovExchangeable`: an exchangeable process is Markov
  exchangeable.
* `TauCeti.Probability.markovExchangeable_of_prefixLaw_singleton_eq`: a process whose finite path
  probabilities factor as an initial weight times a product of transition weights — a Markov chain
  — is Markov exchangeable.
* `TauCeti.Probability.markovExchangeable_pathLaw_iff`: the process-level and path-law
  formulations agree.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable rather than
Markov exchangeable sequences.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Markov exchangeability**, Diaconis and Freedman's partial exchangeability: a measurable
process has equally likely finite paths whenever they have the same starting state and the same
transition counts. The countability and measurable-singleton conjuncts restrict this
singleton-mass formulation to discrete state spaces, where it is non-vacuous and determines the
finite-path laws. -/
def MarkovExchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  Countable α ∧ MeasurableSingletonClass α ∧ (∀ i, AEMeasurable (X i) μ) ∧
    ∀ (n : ℕ) (u v : Fin (n + 1) → α), u 0 = v 0 →
      (∀ a b, transitionCount u a b = transitionCount v a b) →
        prefixLaw μ X (n + 1) {u} = prefixLaw μ X (n + 1) {v}

/-- Constructor from discrete-state instances, coordinatewise a.e. measurability, and invariance
under paths with equal transition counts. -/
theorem MarkovExchangeable.intro [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ)
    (h : ∀ (n : ℕ) (u v : Fin (n + 1) → α), u 0 = v 0 →
      (∀ a b, transitionCount u a b = transitionCount v a b) →
        prefixLaw μ X (n + 1) {u} = prefixLaw μ X (n + 1) {v}) :
    MarkovExchangeable μ X := by
  rw [MarkovExchangeable]
  exact ⟨inferInstance, inferInstance, hX, h⟩

/-- The state space of a Markov exchangeable process is countable. -/
theorem MarkovExchangeable.countable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MarkovExchangeable μ X) : Countable α := by
  rw [MarkovExchangeable] at h
  exact h.1

/-- Singletons in the state space of a Markov exchangeable process are measurable. -/
theorem MarkovExchangeable.measurableSingletonClass {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MarkovExchangeable μ X) : MeasurableSingletonClass α := by
  rw [MarkovExchangeable] at h
  exact h.2.1

/-- Every coordinate of a Markov exchangeable process is a.e. measurable. -/
theorem MarkovExchangeable.aemeasurable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MarkovExchangeable μ X) (i : ℕ) : AEMeasurable (X i) μ := by
  rw [MarkovExchangeable] at h
  exact h.2.2.1 i

/-- Paths with the same starting state and transition counts have the same probability under a
Markov exchangeable process. -/
theorem MarkovExchangeable.prefixLaw_singleton_eq {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MarkovExchangeable μ X) (n : ℕ) (u v : Fin (n + 1) → α) (h0 : u 0 = v 0)
    (hcount : ∀ a b, transitionCount u a b = transitionCount v a b) :
    prefixLaw μ X (n + 1) {u} = prefixLaw μ X (n + 1) {v} := by
  rw [MarkovExchangeable] at h
  exact h.2.2.2 n u v h0 hcount

/-- Simp normal form for `MarkovExchangeable`. -/
@[simp]
theorem markovExchangeable_iff [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} :
    MarkovExchangeable μ X ↔
      (∀ i, AEMeasurable (X i) μ) ∧
        ∀ (n : ℕ) (u v : Fin (n + 1) → α), u 0 = v 0 →
          (∀ a b, transitionCount u a b = transitionCount v a b) →
            prefixLaw μ X (n + 1) {u} = prefixLaw μ X (n + 1) {v} :=
  ⟨fun h => ⟨h.aemeasurable, fun n u v => h.prefixLaw_singleton_eq n u v⟩,
    fun h => MarkovExchangeable.intro h.1 h.2⟩

/-- **An exchangeable process is Markov exchangeable.** Two paths with a common start and common
transition counts are rearrangements of each other, so exchangeability already equates them. -/
theorem Exchangeable.markovExchangeable [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} (h : Exchangeable μ X) (hX : ∀ i, AEMeasurable (X i) μ) :
    MarkovExchangeable μ X := by
  refine MarkovExchangeable.intro hX ?_
  intro n u v h0 hcount
  obtain ⟨σ, hσ⟩ := exists_perm_comp_of_transitionCount_eq h0 hcount
  rw [← hσ]
  exact (h (n + 1)).prefixLaw_singleton_comp (fun i => hX i.val) v σ

/-- **A Markov chain is Markov exchangeable.** The hypothesis is the defining product form of the
finite-dimensional laws of a Markov chain: an initial weight `p₀` at the starting state times the
transition weights `p` along the path. Only the product form matters, not that `p` is a
probability kernel. -/
theorem markovExchangeable_of_prefixLaw_singleton_eq [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ)
    (p₀ : α → ℝ≥0∞) (p : α → α → ℝ≥0∞)
    (h : ∀ (n : ℕ) (w : Fin (n + 1) → α),
      prefixLaw μ X (n + 1) {w} = p₀ (w 0) * ∏ i : Fin n, p (w i.castSucc) (w i.succ)) :
    MarkovExchangeable μ X := by
  refine MarkovExchangeable.intro hX ?_
  intro n u v h0 hcount
  rw [h n u, h n v, h0, prod_eq_of_transitionCount_eq hcount p]

/-- **The process-level and path-law formulations of Markov exchangeability agree.** -/
theorem markovExchangeable_pathLaw_iff [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) :
    MarkovExchangeable (pathLaw μ X) (fun n (x : ℕ → α) => x n) ↔ MarkovExchangeable μ X := by
  constructor
  · intro h
    refine MarkovExchangeable.intro hX ?_
    intro n u v h0 hcount
    rw [← prefixLaw_pathLaw hX]
    exact h.prefixLaw_singleton_eq n u v h0 hcount
  · intro h
    refine MarkovExchangeable.intro (fun i => (measurable_pi_apply i).aemeasurable) ?_
    intro n u v h0 hcount
    rw [prefixLaw_pathLaw hX]
    exact h.prefixLaw_singleton_eq n u v h0 hcount

end Probability

end TauCeti

end

end
