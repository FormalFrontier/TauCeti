/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.ExcursionProcess
public import TauCeti.Probability.Exchangeability.MarkovExchangeable

/-!
# Reordering the excursions of a Markov exchangeable path

A finite path that starts at a state `a₀` and returns to it splits at its visits to `a₀` into
excursions, and `TauCeti.loopPathAt a₀ bs` spells out the path traversing the excursions
`bs : List (List α)` in the listed order. This file proves that a **Markov exchangeable** process
gives the same mass to every ordering of one list of excursions:

```text
bs ~ bs'  →  prefixLaw μ X (n + 1) {loopPathAt a₀ bs} = prefixLaw μ X (n + 1) {loopPathAt a₀ bs'}
```

Markov exchangeability says that the mass of a finite path depends only on its first state and its
transition counts, and reordering excursions changes neither: every excursion is entered at `a₀`
and left back to `a₀`, so the transitions of the whole loop are those of its excursion loops,
gathered in an order that a permutation of the excursions rearranges
(`TauCeti.transitionCount_loopPathAt_eq_of_perm`).

Every finite path returning to its starting state arises this way
(`TauCeti.exists_loopPathAt`), so the statement is a symmetry of *all* the finite-path masses of
such a process, not of a special family of paths;
`TauCeti.Probability.MarkovExchangeable.exists_excursions_prefixLaw_eq` packages the two together.

This is the finite-path symmetry that Diaconis and Freedman's representation theorem for Markov
exchangeable processes rests on: a recurrent Markov exchangeable process returns to its initial
state infinitely often, so its excursions from that state form a genuine sequence of random
finite paths, and the identities below are that sequence's finite-dimensional exchangeability.
The combinatorial excursion process and its reconstruction of a recurrent path segment are set up
in `TauCeti.Combinatorics.Enumerative.ExcursionProcess`.  Assembling the probability identities
below into exchangeability of that process, and running de Finetti on it to exhibit the original
process as a mixture of Markov chains (`TauCeti.Probability.MixedMarkovChain`, whose converse
direction is `TauCeti.Probability.MixedMarkovChainWith.markovExchangeable`), still needs the
recurrence hypothesis at the process level.

## Main results

* `TauCeti.Probability.MarkovExchangeable.prefixLaw_loopPathAt_eq_of_perm`: reordering the
  excursions of a loop does not change its mass.
* `TauCeti.Probability.MarkovExchangeable.prefixLaw_singleton_eq_of_perm_excursions`: the same
  statement read off two finite paths that traverse the same excursions in different orders.
* `TauCeti.Probability.MarkovExchangeable.measure_setOf_loopPathAt_eq_of_perm`: the same statement
  read as an event of the process.
* `TauCeti.Probability.MarkovExchangeable.exists_excursions_prefixLaw_eq`: every finite path that
  returns to its starting state is a loop of excursions avoiding that state, and each reordering
  of them has the same mass.

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

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
variable {μ : Measure Ω} {X : ℕ → Ω → α}

/-- **Reordering the excursions of a loop does not change its mass under a Markov exchangeable
process.** The two paths start at the same state and have the same transition counts, which is
exactly what Markov exchangeability sees. -/
theorem MarkovExchangeable.prefixLaw_loopPathAt_eq_of_perm (h : MarkovExchangeable μ X) (a₀ : α)
    {bs bs' : List (List α)} (hperm : bs.Perm bs') {n : ℕ} (hn : loopSteps bs = n) :
    prefixLaw μ X (n + 1) {fun i : Fin (n + 1) => loopPathAt a₀ bs i.val} =
      prefixLaw μ X (n + 1) {fun i : Fin (n + 1) => loopPathAt a₀ bs' i.val} :=
  h.prefixLaw_singleton_eq n _ _ (by simp) fun a b =>
    transitionCount_loopPathAt_eq_of_perm a₀ hperm hn a b

/-- **Two finite paths that traverse the same excursions in different orders are equally likely.**
The user-facing form of `TauCeti.Probability.MarkovExchangeable.prefixLaw_loopPathAt_eq_of_perm`:
the hypotheses say that `u` and `v` both start at `a₀` and run through the excursions `bs`,
respectively `bs'`, and `TauCeti.exists_loopPathAt` supplies such a list for every finite path
that returns to its starting state. -/
theorem MarkovExchangeable.prefixLaw_singleton_eq_of_perm_excursions (h : MarkovExchangeable μ X)
    (a₀ : α) {n : ℕ} {u v : Fin (n + 1) → α} {bs bs' : List (List α)} (hperm : bs.Perm bs')
    (hn : loopSteps bs = n) (hu : ∀ i : Fin (n + 1), loopPathAt a₀ bs i.val = u i)
    (hv : ∀ i : Fin (n + 1), loopPathAt a₀ bs' i.val = v i) :
    prefixLaw μ X (n + 1) {u} = prefixLaw μ X (n + 1) {v} := by
  rw [← funext hu, ← funext hv]
  exact h.prefixLaw_loopPathAt_eq_of_perm a₀ hperm hn

/-- The mass of a finite path, as the measure of the event that the process spells it out. -/
private theorem prefixLaw_singleton_eq_measure [MeasurableSingletonClass α]
    (hX : ∀ i, AEMeasurable (X i) μ) {n : ℕ} (w : Fin n → α) :
    prefixLaw μ X n {w} = μ {ω | ∀ i : Fin n, X i.val ω = w i} := by
  rw [prefixLaw_def, blockLaw_apply_of_measurable μ X (fun i : Fin n => i.val)
    (fun i => hX i.val) (measurableSet_singleton w)]
  exact congrArg μ (Set.ext fun ω => by simp [funext_iff, eq_comm])

/-- **Reordering the excursions of a loop does not change the probability that the process
traverses it.** The event-level form of
`TauCeti.Probability.MarkovExchangeable.prefixLaw_loopPathAt_eq_of_perm`. -/
theorem MarkovExchangeable.measure_setOf_loopPathAt_eq_of_perm (h : MarkovExchangeable μ X)
    (a₀ : α) {bs bs' : List (List α)} (hperm : bs.Perm bs') {n : ℕ} (hn : loopSteps bs = n) :
    μ {ω | ∀ i ≤ n, X i ω = loopPathAt a₀ bs i} =
      μ {ω | ∀ i ≤ n, X i ω = loopPathAt a₀ bs' i} := by
  have := h.countable
  have := h.measurableSingletonClass
  have key := h.prefixLaw_loopPathAt_eq_of_perm a₀ hperm hn
  rw [prefixLaw_singleton_eq_measure h.aemeasurable,
    prefixLaw_singleton_eq_measure h.aemeasurable] at key
  convert key using 2 <;>
    exact Set.ext fun ω => ⟨fun hω i => hω i.val (by omega), fun hω i hi => hω ⟨i, by omega⟩⟩

/-- **The finite-path symmetry of a Markov exchangeable process.** Every finite path `w` that
returns to its starting state is the loop of a list of excursions, none of which visits that
state, and every reordering of those excursions has the same mass as `w` itself. -/
theorem MarkovExchangeable.exists_excursions_prefixLaw_eq (h : MarkovExchangeable μ X) {n : ℕ}
    (w : Fin (n + 1) → α) (hw : w (Fin.last n) = w 0) :
    ∃ bs : List (List α), loopSteps bs = n ∧ (∀ e ∈ bs, w 0 ∉ e) ∧
      (∀ i : Fin (n + 1), loopPathAt (w 0) bs i.val = w i) ∧
      ∀ bs' : List (List α), bs.Perm bs' →
        prefixLaw μ X (n + 1) {fun i : Fin (n + 1) => loopPathAt (w 0) bs' i.val} =
          prefixLaw μ X (n + 1) {w} := by
  obtain ⟨bs, hn, havoid, hval⟩ := exists_loopPathAt w hw
  exact ⟨bs, hn, havoid, hval, fun bs' hperm =>
    h.prefixLaw_singleton_eq_of_perm_excursions (w 0) hperm.symm
      ((loopSteps_eq_of_perm hperm).symm.trans hn) (fun _ => rfl) hval⟩

end Probability

end TauCeti

end

end
