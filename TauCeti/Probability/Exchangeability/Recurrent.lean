/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.SuccessorArray
public import TauCeti.Probability.Exchangeability.MarkovExchangeable
public import TauCeti.Probability.Exchangeability.Stationary
-- Non-public: Poincaré recurrence for a conservative map is used only inside proofs.
import Mathlib.Dynamics.Ergodic.Conservative

/-!
# Recurrent processes

A process `X : ℕ → Ω → α` is **recurrent** when, almost surely, every state it ever visits it
visits infinitely often:

```text
∀ᵐ ω ∂μ, ∀ k, ∃ᶠ n in atTop, X n ω = X k ω
```

This is the hypothesis of the Diaconis–Freedman representation theorem — a *recurrent* Markov
exchangeable process is a mixture of Markov chains — and it is what makes the successor-array
change of variables of `TauCeti/Probability/Exchangeability/SuccessorArray.lean` lossless. That
encoding reads a path as its initial state together with, for each state `a`, the list of values
following the successive visits to `a`. Off a recurrent path some of those rows run out and the
reconstruction reads `Nat.nth`'s junk value instead of a genuine successor; on a recurrent path
every row is an infinite list of genuine transitions, which is the form the representation
theorem consumes.

The main theorem is that recurrence is automatic for a *stationary* process on a countable state
space (`recurrent_of_measurePreserving_shift`): it is Poincaré recurrence for the one-sided shift,
applied to the countably many coordinate events `{x | x 0 = a}` at once. Contractable — hence
exchangeable — processes are stationary, so they are recurrent (`Contractable.recurrent`,
`Exchangeable.recurrent`). A Markov exchangeable process need not be: the deterministic path
`false, true, true, …` of `absorbedWalk` is a Markov chain, hence Markov exchangeable, and visits
`false` exactly once.

## Main definitions

* `TauCeti.Probability.Recurrent` — almost surely, every visited state is visited infinitely
  often.
* `TauCeti.Probability.absorbedWalk` — the deterministic path that leaves `false` at time `1` and
  stays at `true`.

## Main results

* `TauCeti.Probability.recurrent_iff_ae_forall_state` — the state-indexed reading of the
  definition.
* `TauCeti.Probability.recurrent_of_measurePreserving_shift` — a process with a shift-invariant
  path law on a countable state space is recurrent, and its corollaries
  `TauCeti.Probability.Contractable.recurrent` and `TauCeti.Probability.Exchangeable.recurrent`.
* `TauCeti.Probability.recurrent_pathLaw_iff` — the process-level and path-law readings agree.
* `TauCeti.Probability.Recurrent.ae_apply_visitTime`,
  `TauCeti.Probability.Recurrent.ae_strictMono_visitTime`,
  `TauCeti.Probability.Recurrent.ae_visitCount_visitTime`,
  `TauCeti.Probability.Recurrent.ae_tendsto_visitCount_atTop` — the rows of the successor array of
  a recurrent process are genuine: the visit times of a visited state are an infinite strictly
  increasing list of times at which the process really is at that state, and they exhaust it.
* `TauCeti.Probability.Recurrent.ae_exists_visitCount_eq` and
  `TauCeti.Probability.Recurrent.ae_exists_successorArray_eq` — every cell of a visited row of the
  successor array is realized by an actual time, and holds an actual transition out of that
  state.
* `TauCeti.Probability.absorbedWalk_markovExchangeable` and
  `TauCeti.Probability.not_recurrent_absorbedWalk` — recurrence is a genuine extra hypothesis on a
  Markov exchangeable process.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".

Mathlib's `MeasureTheory.Conservative` is recurrence of a *map* — the Poincaré recurrence theorem
— and is consumed here rather than reproved; recurrence of a *process* in the above sense is not
in Mathlib. No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable
rather than Markov exchangeable sequences.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

section Defs

variable {Ω α : Type*} [MeasurableSpace Ω]

/-- A process is **recurrent** when, almost surely, every state it visits it visits infinitely
often. This is Diaconis and Freedman's standing hypothesis on a Markov exchangeable process. -/
def Recurrent (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ᶠ n in atTop, X n ω = X k ω

variable {μ : Measure Ω} {X Y : ℕ → Ω → α}

/-- The defining equation of `Recurrent`. -/
theorem recurrent_iff :
    Recurrent μ X ↔ ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ᶠ n in atTop, X n ω = X k ω :=
  Iff.rfl

/-- **The state-indexed reading of recurrence.** Almost surely, every state the process attains
it attains infinitely often. -/
theorem recurrent_iff_ae_forall_state :
    Recurrent μ X ↔
      ∀ᵐ ω ∂μ, ∀ a : α, (∃ k, X k ω = a) → ∃ᶠ n in atTop, X n ω = a := by
  constructor
  · intro h
    filter_upwards [h] with ω hω a ha
    obtain ⟨k, hk⟩ := ha
    exact hk ▸ hω k
  · intro h
    filter_upwards [h] with ω hω k
    exact hω (X k ω) ⟨k, rfl⟩

/-- The set of times at which a recurrent process revisits any given one of its states is
infinite. -/
theorem Recurrent.ae_infinite_setOf_eq (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, {n | X n ω = X k ω}.Infinite := by
  filter_upwards [h] with ω hω k
  exact Nat.frequently_atTop_iff_infinite.mp (hω k)

/-- Every state of a recurrent process recurs after every time. -/
theorem Recurrent.ae_exists_ge (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k N : ℕ, ∃ n, N ≤ n ∧ X n ω = X k ω := by
  filter_upwards [h] with ω hω k N
  obtain ⟨n, hn, hxn⟩ := (frequently_atTop.mp (hω k)) N
  exact ⟨n, hn, hxn⟩

/-- Recurrence only depends on the process up to almost-everywhere equality of its
coordinates. -/
theorem Recurrent.congr (h : Recurrent μ X) (hXY : ∀ n, X n =ᵐ[μ] Y n) : Recurrent μ Y := by
  have hall : ∀ᵐ ω ∂μ, ∀ n, X n ω = Y n ω := ae_all_iff.2 hXY
  filter_upwards [h, hall] with ω hω heq k
  refine (hω k).mono fun n hn => ?_
  rw [← heq n, ← heq k]
  exact hn

/-- Recurrence is inherited by every coordinatewise pushforward: a repeated state stays
repeated. -/
theorem Recurrent.map_values {β : Type*} (h : Recurrent μ X) (f : α → β) :
    Recurrent μ fun n ω => f (X n ω) := by
  filter_upwards [h] with ω hω k
  exact (hω k).mono fun n hn => by rw [hn]

end Defs

section Stationary

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Poincaré recurrence on path space.** A shift-invariant law on the paths of a countable
state space gives full mass to the paths that revisit each of their states infinitely often.

The one-sided shift is measure preserving, hence conservative, so almost every path whose orbit
meets the coordinate event `{x | x 0 = a}` meets it infinitely often; countability of the state
space lets a single null set serve all `a` at once. -/
theorem ae_forall_frequently_apply_eq_of_measurePreserving_shift
    [Countable α] [MeasurableSingletonClass α] {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]
    (h : MeasurePreserving (shift α) ρ ρ) :
    ∀ᵐ x ∂ρ, ∀ k : ℕ, ∃ᶠ n in atTop, x n = x k := by
  have hcons : Conservative (shift α) ρ := h.conservative
  have key : ∀ a : α, ∀ᵐ x ∂ρ, ∀ k : ℕ, x k = a → ∃ᶠ n in atTop, x n = a := by
    intro a
    have hpre : {x : ℕ → α | x 0 = a} = (fun x : ℕ → α => x 0) ⁻¹' {a} := by
      ext x
      simp
    have hs : MeasurableSet {x : ℕ → α | x 0 = a} :=
      hpre ▸ (measurable_pi_apply 0) (measurableSet_singleton a)
    filter_upwards [hcons.ae_forall_image_mem_imp_frequently_image_mem hs.nullMeasurableSet]
      with x hx k hk
    have hxk := hx k (by simpa using hk)
    simpa using hxk
  filter_upwards [ae_all_iff.2 key] with x hx k
  exact hx (x k) k rfl

/-- **A stationary process on a countable state space is recurrent.** -/
theorem recurrent_of_measurePreserving_shift [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ)
    (h : MeasurePreserving (shift α) (pathLaw μ X) (pathLaw μ X)) :
    Recurrent μ X := by
  have hfin : IsFiniteMeasure (pathLaw μ X) := by rw [pathLaw_def]; infer_instance
  have hmap : AEMeasurable (fun ω i => X i ω) μ := aemeasurable_pi_lambda _ hX
  have hpath := ae_forall_frequently_apply_eq_of_measurePreserving_shift h
  rw [pathLaw_def] at hpath
  exact ae_of_ae_map hmap hpath

/-- **A contractable process on a countable state space is recurrent.** -/
theorem Contractable.recurrent [Countable α] [MeasurableSingletonClass α] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    Recurrent μ X :=
  recurrent_of_measurePreserving_shift hX_meas (hX.measurePreserving_shift hX_meas)

/-- **An exchangeable process on a countable state space is recurrent.** Together with
`Exchangeable.markovExchangeable` this says that the Diaconis–Freedman hypotheses hold for every
exchangeable process on a countable state space. -/
theorem Exchangeable.recurrent [Countable α] [MeasurableSingletonClass α] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Exchangeable μ X)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    Recurrent μ X :=
  recurrent_of_measurePreserving_shift hX_meas (hX.measurePreserving_shift hX_meas)

end Stationary

section PathLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The recurrent paths of a countable state space form a measurable set: they are cut out by
countably many coordinate coincidences, each measurable by Mathlib's `measurableSet_eq_fun`. -/
theorem measurableSet_setOf_forall_frequently_apply_eq [Countable α]
    [MeasurableSingletonClass α] :
    MeasurableSet {x : ℕ → α | ∀ k : ℕ, ∃ᶠ n in atTop, x n = x k} := by
  have hcover : {x : ℕ → α | ∀ k : ℕ, ∃ᶠ n in atTop, x n = x k} =
      ⋂ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ _ : N ≤ n, {x : ℕ → α | x n = x k} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, frequently_atTop, exists_prop]
  rw [hcover]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      measurableSet_eq_fun (measurable_pi_apply n) (measurable_pi_apply k)

/-- **The process-level and path-law formulations of recurrence agree.** -/
theorem recurrent_pathLaw_iff [Countable α] [MeasurableSingletonClass α] {μ : Measure Ω}
    {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ) :
    Recurrent (pathLaw μ X) (fun n (x : ℕ → α) => x n) ↔ Recurrent μ X := by
  have hmap : AEMeasurable (fun ω i => X i ω) μ := aemeasurable_pi_lambda _ hX
  rw [Recurrent, Recurrent, pathLaw_def,
    ae_map_iff hmap measurableSet_setOf_forall_frequently_apply_eq]

end PathLaw

section SuccessorArray

variable {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → α}

/-- **The visit times of a visited state are genuine visits.** Off a recurrent path the later
entries of `visitTime` are `Nat.nth`'s junk value; on one they are the times at which the process
really is at that state. -/
theorem Recurrent.ae_apply_visitTime (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k j : ℕ, X (visitTime (fun n => X n ω) (X k ω) j) ω = X k ω := by
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω k j
  simpa only [visitTime_def] using Nat.nth_mem_of_infinite (hω k) j

/-- The visit times of a visited state of a recurrent process are strictly increasing, so the
corresponding row of the successor array lists distinct times in order. -/
theorem Recurrent.ae_strictMono_visitTime (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, StrictMono (visitTime (fun n => X n ω) (X k ω)) := by
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω k
  have hfun : visitTime (fun n => X n ω) (X k ω) = Nat.nth fun i => X i ω = X k ω := by
    funext j
    exact visitTime_def _ _ _
  rw [hfun]
  exact Nat.nth_strictMono (hω k)

/-- The `j`-th visit of a recurrent process to one of its states really is preceded by exactly
`j` earlier visits. -/
theorem Recurrent.ae_visitCount_visitTime (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k j : ℕ,
      visitCount (fun n => X n ω) (X k ω) (visitTime (fun n => X n ω) (X k ω) j) = j := by
  classical
  filter_upwards [h.ae_infinite_setOf_eq] with ω hω k j
  rw [visitCount_eq_count, visitTime_def]
  exact Nat.count_nth_of_infinite (hω k) j

/-- **Each visited row of the successor array is infinite.** A recurrent process accumulates
unboundedly many visits to every state it attains. -/
theorem Recurrent.ae_tendsto_visitCount_atTop (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, Tendsto (visitCount (fun n => X n ω) (X k ω)) atTop atTop := by
  filter_upwards [h.ae_visitCount_visitTime] with ω hω k
  refine tendsto_atTop_atTop.2 fun b => ⟨visitTime (fun n => X n ω) (X k ω) b, fun n hn => ?_⟩
  calc b = visitCount (fun n => X n ω) (X k ω) (visitTime (fun n => X n ω) (X k ω) b) :=
        (hω k b).symm
    _ ≤ visitCount (fun n => X n ω) (X k ω) n := visitCount_monotone _ _ hn

/-- **Every cell of a visited row is realized by a time.** For a recurrent process the index `j`
of a row of the successor array is the number of earlier visits at an actual time. -/
theorem Recurrent.ae_exists_visitCount_eq (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k j : ℕ, ∃ n, X n ω = X k ω ∧ visitCount (fun n => X n ω) (X k ω) n = j := by
  filter_upwards [h.ae_apply_visitTime, h.ae_visitCount_visitTime] with ω h₁ h₂ k j
  exact ⟨_, h₁ k j, h₂ k j⟩

/-- **No junk in a visited row of the successor array.** Every entry of the row of a visited state
is the value the process takes right after an actual visit to that state. -/
theorem Recurrent.ae_exists_successorArray_eq (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k j : ℕ,
      ∃ n, X n ω = X k ω ∧ successorArray (fun n => X n ω) (X k ω) j = X (n + 1) ω := by
  filter_upwards [h.ae_apply_visitTime] with ω h₁ k j
  exact ⟨_, h₁ k j, successorArray_def _ _ _⟩

end SuccessorArray

section AbsorbedWalk

/-- The deterministic path `false, true, true, …`, on the one-point sample space. It is the
Markov chain that leaves `false` at time `1` and is then absorbed at `true`. -/
@[expose]
def absorbedWalk : ℕ → Unit → Bool := fun n _ => decide (n ≠ 0)

@[simp]
theorem absorbedWalk_apply (n : ℕ) (u : Unit) : absorbedWalk n u = decide (n ≠ 0) :=
  rfl

/-- **The absorbed walk has the finite-dimensional laws of a Markov chain.** A path of length
`n + 1` is possible only if it starts at `false` and is `true` from time `1` on. -/
theorem absorbedWalk_prefixLaw_singleton (n : ℕ) (w : Fin (n + 1) → Bool) :
    prefixLaw (Measure.dirac ()) absorbedWalk (n + 1) {w} =
      (if w 0 = false then 1 else 0) *
        ∏ i : Fin n, (if w i.succ = true then 1 else 0 : ℝ≥0∞) := by
  classical
  have hmap : prefixLaw (Measure.dirac ()) absorbedWalk (n + 1) {w} =
      Measure.dirac () ((fun (u : Unit) (i : Fin (n + 1)) => absorbedWalk i.val u) ⁻¹' {w}) := by
    rw [prefixLaw_def, blockLaw_def,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  by_cases hw : w 0 = false ∧ ∀ i : Fin n, w i.succ = true
  · have hval : ∀ i : Fin (n + 1), w i = decide (i.val ≠ 0) := by
      intro i
      induction i using Fin.cases with
      | zero => simpa using hw.1
      | succ j => simpa using hw.2 j
    have hset : (fun (u : Unit) (i : Fin (n + 1)) => absorbedWalk i.val u) ⁻¹' {w} =
        Set.univ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true, funext_iff,
        absorbedWalk_apply]
      exact fun i => (hval i).symm
    have hprod : (∏ i : Fin n, (if w i.succ = true then 1 else 0 : ℝ≥0∞)) = 1 :=
      Finset.prod_eq_one fun i _ => by simp [hw.2 i]
    rw [hmap, hset, hprod, ite_eq_left hw.1, measure_univ, one_mul]
  · have hset : (fun (u : Unit) (i : Fin (n + 1)) => absorbedWalk i.val u) ⁻¹' {w} = ∅ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        funext_iff, absorbedWalk_apply]
      intro hcontra
      refine hw ⟨by simpa using (hcontra 0).symm, fun i => ?_⟩
      simpa using (hcontra i.succ).symm
    rcases not_and_or.mp hw with h0 | hstep
    · rw [hmap, hset, measure_empty, ite_eq_right h0, zero_mul]
    · obtain ⟨i, hi⟩ := not_forall.mp hstep
      have hprod : (∏ i : Fin n, (if w i.succ = true then 1 else 0 : ℝ≥0∞)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      rw [hmap, hset, measure_empty, hprod, mul_zero]

/-- **The absorbed walk is Markov exchangeable**, being a Markov chain. -/
theorem absorbedWalk_markovExchangeable :
    MarkovExchangeable (Measure.dirac ()) absorbedWalk :=
  markovExchangeable_of_prefixLaw_singleton_eq
    (fun _ => measurable_const.aemeasurable)
    (fun a => if a = false then 1 else 0) (fun _ b => if b = true then 1 else 0)
    absorbedWalk_prefixLaw_singleton

/-- **The absorbed walk is not recurrent**: it visits `false` only at time `0`. Together with
`absorbedWalk_markovExchangeable` this shows that recurrence is a genuine extra hypothesis on a
Markov exchangeable process, in contrast with `Exchangeable.recurrent`. -/
theorem not_recurrent_absorbedWalk : ¬ Recurrent (Measure.dirac ()) absorbedWalk := by
  intro h
  rw [Recurrent, MeasureTheory.ae_dirac_eq, Filter.eventually_pure] at h
  have h0 := h 0
  rw [Nat.frequently_atTop_iff_infinite] at h0
  refine h0 (Set.Finite.subset (Set.finite_singleton 0) ?_)
  intro n hn
  simp only [Set.mem_ofPred_eq, absorbedWalk_apply, decide_eq_decide] at hn
  simpa using hn

end AbsorbedWalk

end Probability

end TauCeti

end

end
