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

open Finset MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Markov exchangeability**, Diaconis and Freedman's partial exchangeability: two finite paths
with the same starting state and the same transition counts are equally likely. -/
@[expose]
def MarkovExchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (n : ℕ) (u v : Fin (n + 1) → α), u 0 = v 0 →
    (∀ a b, transitionCount u a b = transitionCount v a b) →
      prefixLaw μ X (n + 1) {u} = prefixLaw μ X (n + 1) {v}

/-- Simp normal form for `MarkovExchangeable`. -/
@[simp]
theorem markovExchangeable_iff {μ : Measure Ω} {X : ℕ → Ω → α} :
    MarkovExchangeable μ X ↔
      ∀ (n : ℕ) (u v : Fin (n + 1) → α), u 0 = v 0 →
        (∀ a b, transitionCount u a b = transitionCount v a b) →
          prefixLaw μ X (n + 1) {u} = prefixLaw μ X (n + 1) {v} :=
  Iff.rfl

/-- Under finite exchangeability at `n`, rearranging a path leaves its probability unchanged. -/
theorem ExchangeableAt.prefixLaw_singleton_comp [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ} (h : ExchangeableAt μ X n)
    (hX : ∀ i, AEMeasurable (X i) μ) (w : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    prefixLaw μ X n {w ∘ σ} = prefixLaw μ X n {w} := by
  have hmeas : Measurable fun x : Fin n → α => fun i => x (σ⁻¹ i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (σ⁻¹ i)
  have hmap : (prefixLaw μ X n).map (fun x : Fin n → α => fun i => x (σ⁻¹ i)) =
      prefixLaw μ X n := by
    conv_lhs => rw [prefixLaw_def]
    rw [map_blockLaw_reindex μ (fun i : Fin n => i.val) (fun i => σ⁻¹ i) fun j => hX j.val]
    exact h σ⁻¹
  conv_rhs => rw [← hmap]
  rw [Measure.map_apply hmeas (measurableSet_singleton w)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Function.comp_apply]
  refine ⟨fun hx j => ?_, fun hx i => ?_⟩
  · simpa using hx (σ⁻¹ j)
  · simpa using hx (σ i)

/-- **An exchangeable process is Markov exchangeable.** Two paths with a common start and common
transition counts are rearrangements of each other, so exchangeability already equates them. -/
theorem Exchangeable.markovExchangeable [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} (h : Exchangeable μ X) (hX : ∀ i, AEMeasurable (X i) μ) :
    MarkovExchangeable μ X := by
  intro n u v h0 hcount
  obtain ⟨σ, hσ⟩ := exists_perm_comp_of_transitionCount_eq h0 hcount
  rw [← hσ]
  exact (h (n + 1)).prefixLaw_singleton_comp hX v σ

/-- **A Markov chain is Markov exchangeable.** The hypothesis is the defining product form of the
finite-dimensional laws of a Markov chain: an initial weight `p₀` at the starting state times the
transition weights `p` along the path. Only the product form matters, not that `p` is a
probability kernel. -/
theorem markovExchangeable_of_prefixLaw_singleton_eq {μ : Measure Ω} {X : ℕ → Ω → α}
    (p₀ : α → ℝ≥0∞) (p : α → α → ℝ≥0∞)
    (h : ∀ (n : ℕ) (w : Fin (n + 1) → α),
      prefixLaw μ X (n + 1) {w} = p₀ (w 0) * ∏ i : Fin n, p (w i.castSucc) (w i.succ)) :
    MarkovExchangeable μ X := by
  classical
  intro n u v h0 hcount
  set S : Finset α := image u univ ∪ image v univ
  have hSu : ∀ i, u i ∈ S := fun i => mem_union_left _ (mem_image_of_mem u (mem_univ i))
  have hSv : ∀ i, v i ∈ S := fun i => mem_union_right _ (mem_image_of_mem v (mem_univ i))
  rw [h n u, h n v, h0, prod_transitionCount u hSu p, prod_transitionCount v hSv p]
  exact congrArg _ (prod_congr rfl fun ab _ => by rw [hcount ab.1 ab.2])

/-- The prefix laws of a path law are the prefix laws of the process. -/
theorem prefixLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) : prefixLaw (pathLaw μ X) (fun n (x : ℕ → α) => x n) n = prefixLaw μ X n := by
  rw [prefixLaw_def, blockLaw_def,
    ← map_prefixProj_pathLaw μ (aemeasurable_pi_lambda (fun ω => fun i => X i ω) hX) n]
  rfl

/-- **The process-level and path-law formulations of Markov exchangeability agree.** -/
theorem markovExchangeable_pathLaw_iff {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) :
    MarkovExchangeable (pathLaw μ X) (fun n (x : ℕ → α) => x n) ↔ MarkovExchangeable μ X := by
  simp only [markovExchangeable_iff, prefixLaw_pathLaw hX]

end Probability

end TauCeti

end

end
