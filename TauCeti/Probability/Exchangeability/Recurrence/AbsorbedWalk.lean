/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac
public import TauCeti.Probability.Exchangeability.MarkovExchangeable
public import TauCeti.Probability.Recurrent

/-!
# A nonrecurrent Markov exchangeable process

The deterministic path `false, true, true, …` is a Markov chain and hence Markov exchangeable,
but it visits `false` only once. Thus recurrence is a genuine additional hypothesis in the
Diaconis–Freedman representation theorem.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

section AbsorbedWalk

/-- The deterministic path `false, true, true, …`, on the one-point sample space. It is the
Markov chain that leaves `false` at time `1` and is then absorbed at `true`. -/
def absorbedWalk : ℕ → Unit → Bool := fun n _ => decide (n ≠ 0)

@[simp]
theorem absorbedWalk_apply (n : ℕ) (u : Unit) : absorbedWalk n u = decide (n ≠ 0) :=
  (rfl)

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
  rw [recurrent_def, MeasureTheory.ae_dirac_eq, Filter.eventually_pure] at h
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
