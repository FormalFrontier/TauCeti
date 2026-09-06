/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.TransitionCount
public import TauCeti.Probability.Exchangeability.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

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
* `TauCeti.Probability.markovExchangeable_iff_map_prefixLaw_perm_eq`: Markov exchangeability is
  invariance of each prefix law under every permutation preserving the initial state and transition
  counts.
* `TauCeti.Probability.MarkovExchangeable.prefixLaw_apply_eq_of_equiv`: more generally, two sets
  of finite paths have the same mass when a transition-count-preserving equivalence pairs them.
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

/-- **Equinumerous Markov-equivalence classes have equal prefix-law mass.** More precisely, an
equivalence between two sets of finite paths preserves their mass when it pairs paths with the same
initial state and directed transition counts.

This is the form used by finite last-exit reconstruction: the reconstruction gives an equivalence
between two collections of admissible prefixes, rather than a permutation of every finite path. -/
theorem MarkovExchangeable.prefixLaw_apply_eq_of_equiv {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MarkovExchangeable μ X) (n : ℕ) {s t : Set (Fin (n + 1) → α)} (e : s ≃ t)
    (h0 : ∀ w, (e w).1 0 = w.1 0)
    (hcount : ∀ w a b, transitionCount (e w).1 a b = transitionCount w.1 a b) :
    prefixLaw μ X (n + 1) s = prefixLaw μ X (n + 1) t := by
  let _ : Countable α := h.countable
  have : MeasurableSingletonClass α := h.measurableSingletonClass
  let θ := prefixLaw μ X (n + 1)
  have hs : (∑' w : s, θ ({w.1} : Set (Fin (n + 1) → α))) = θ s := by
    simpa only [Set.preimage_id, id_eq] using
      tsum_measure_preimage_singleton (μ := θ) (s := s) (Set.to_countable s)
        (f := id) (fun w _ => measurableSet_singleton w)
  have ht : (∑' w : t, θ ({w.1} : Set (Fin (n + 1) → α))) = θ t := by
    simpa only [Set.preimage_id, id_eq] using
      tsum_measure_preimage_singleton (μ := θ) (s := t) (Set.to_countable t)
        (f := id) (fun w _ => measurableSet_singleton w)
  calc
    prefixLaw μ X (n + 1) s = ∑' w : s, θ ({w.1} : Set (Fin (n + 1) → α)) := hs.symm
    _ = ∑' w : s, θ ({(e w).1} : Set (Fin (n + 1) → α)) := by
      apply tsum_congr
      intro w
      exact h.prefixLaw_singleton_eq n w.1 (e w).1 (h0 w).symm fun a b =>
        (hcount w a b).symm
    _ = ∑' w : t, θ ({w.1} : Set (Fin (n + 1) → α)) :=
      e.tsum_eq (fun w : t => θ ({w.1} : Set (Fin (n + 1) → α)))
    _ = prefixLaw μ X (n + 1) t := ht

/-- **A transition-count-preserving permutation preserves a Markov-exchangeable prefix law.**
The permutation may rearrange finite paths in any way, provided it preserves their initial state
and every directed transition count. This is the setwise form of Markov exchangeability used when
a deterministic reconstruction permutes all paths in a finite Markov-exchangeability class. -/
theorem MarkovExchangeable.map_prefixLaw_perm_eq {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MarkovExchangeable μ X) (n : ℕ)
    (e : Equiv.Perm (Fin (n + 1) → α)) (h0 : ∀ w, e w 0 = w 0)
    (hcount : ∀ w a b, transitionCount (e w) a b = transitionCount w a b) :
    Measure.map (α := Fin (n + 1) → α) (β := Fin (n + 1) → α) e
      (prefixLaw (α := α) μ X (n + 1)) = prefixLaw (α := α) μ X (n + 1) := by
  let _ : Countable α := h.countable
  have : MeasurableSingletonClass α := h.measurableSingletonClass
  rw [Measure.ext_iff_singleton]
  intro w
  rw [Measure.map_apply_of_aemeasurable
    (Measurable.of_discrete : Measurable (e : (Fin (n + 1) → α) → Fin (n + 1) → α)).aemeasurable
    (measurableSet_singleton w)]
  have hpre : e ⁻¹' ({w} : Set (Fin (n + 1) → α)) = {e.symm w} := by
    ext v
    exact e.eq_symm_apply.symm
  rw [hpre]
  apply h.prefixLaw_singleton_eq n (e.symm w) w
  · rw [← h0 (e.symm w), e.apply_symm_apply]
  · intro a b
    rw [← hcount (e.symm w) a b, e.apply_symm_apply]

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

/-- **Permutation-invariance characterization of Markov exchangeability.** A measurable process
is Markov exchangeable exactly when each finite prefix law is invariant under every permutation of
path words that preserves the initial state and every directed transition count.

This is stronger as an interface than equality of singleton masses: it transports arbitrary
events at once. Conversely, swapping any two words in one Markov-exchangeability class recovers the
defining singleton equality. -/
theorem markovExchangeable_iff_map_prefixLaw_perm_eq [Countable α]
    [MeasurableSingletonClass α] {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) :
    MarkovExchangeable μ X ↔
      ∀ (n : ℕ) (e : Equiv.Perm (Fin (n + 1) → α)),
        (∀ w, e w 0 = w 0) →
        (∀ w a b, transitionCount (e w) a b = transitionCount w a b) →
          Measure.map (α := Fin (n + 1) → α) (β := Fin (n + 1) → α) e
            (prefixLaw (α := α) μ X (n + 1)) = prefixLaw (α := α) μ X (n + 1) := by
  constructor
  · intro h n e h0 hcount
    exact h.map_prefixLaw_perm_eq n e h0 hcount
  · intro h
    classical
    refine MarkovExchangeable.intro hX fun n u v h0 hcount => ?_
    by_cases huv : u = v
    · rw [huv]
    let e : Equiv.Perm (Fin (n + 1) → α) := Equiv.swap u v
    have he0 : ∀ w, e w 0 = w 0 := by
      intro w
      by_cases hwu : w = u
      · subst w
        rw [show e u = v by simp [e]]
        exact h0.symm
      by_cases hwv : w = v
      · subst w
        rw [show e v = u by simp [e]]
        exact h0
      rw [show e w = w by exact Equiv.swap_apply_of_ne_of_ne hwu hwv]
    have hecount : ∀ w a b, transitionCount (e w) a b = transitionCount w a b := by
      intro w a b
      by_cases hwu : w = u
      · subst w
        rw [show e u = v by simp [e]]
        exact (hcount a b).symm
      by_cases hwv : w = v
      · subst w
        rw [show e v = u by simp [e]]
        exact hcount a b
      rw [show e w = w by exact Equiv.swap_apply_of_ne_of_ne hwu hwv]
    have hinv := h n e he0 hecount
    have hset := congrArg
      (fun θ : Measure (Fin (n + 1) → α) => θ ({v} : Set (Fin (n + 1) → α))) hinv
    rw [Measure.map_apply_of_aemeasurable
      (Measurable.of_discrete : Measurable
        (e : (Fin (n + 1) → α) → Fin (n + 1) → α)).aemeasurable
      (measurableSet_singleton v)] at hset
    have hpre : e ⁻¹' ({v} : Set (Fin (n + 1) → α)) = {u} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, e]
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    rwa [hpre] at hset

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
