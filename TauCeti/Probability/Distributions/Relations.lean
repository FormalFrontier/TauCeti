/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
import TauCeti.MeasureTheory.Order.Lattice

/-!
# The extremes of an independent identically distributed family

Let `X : ι → Ω → ℝ` be an independent family over a nonempty finite index type, all of whose
members have the same law `μ`. This file computes the law of the two extremes of the family: the
maximum `Finset.univ.sup' Finset.univ_nonempty fun i => X i ω` and the minimum
`Finset.univ.inf' Finset.univ_nonempty fun i => X i ω`. Writing `d = Fintype.card ι`, the
cumulative distribution functions are `(cdf μ x) ^ d` and `1 - (1 - cdf μ x) ^ d`.

Both extremes are taken over `Finset.univ` together with its nonemptiness proof, so neither
formula acquires the default value that an empty family would force on a `Finset.sup` or a
`Finset.inf`: `d = 0` never occurs.

**One event identity does the work.** The maximum is at most `x` exactly when every member is
(`Finset.sup'_le_iff`), and `x` is below the minimum exactly when it is below every member
(`Finset.lt_inf'_iff`). Independence turns each of those intersections into a product of `d`
equal factors, which is where the two powers come from. The minimum is then read off its
complementary event, which is why its formula is the one with the two subtractions.

`cdf_min_iid` specialises to the exponential family as `hasLaw_min_iid_expMeasure`: the minimum
of `d` i.i.d. exponentials of rate `r` is exponential of rate `d * r`.

## Main results

* `TauCeti.Probability.measure_setOf_max_le_iid`, `TauCeti.Probability.measureReal_setOf_max_le_iid`
  — the maximum is at most `x` with probability `(cdf μ x) ^ d`;
* `TauCeti.Probability.measure_setOf_lt_min_iid`,
  `TauCeti.Probability.measureReal_setOf_min_le_iid` — the minimum exceeds `x` with probability
  `(1 - cdf μ x) ^ d`, hence is at most `x` with probability `1 - (1 - cdf μ x) ^ d`;
* `TauCeti.Probability.cdf_max_iid`, `TauCeti.Probability.cdf_min_iid` — the same two formulas for
  the laws of the two extremes.

A general theory of order statistics is outside the scope of the roadmap target below.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 4, item 6,
  **Finite minima and maxima**.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Fintype ι] [Nonempty ι] {P : Measure Ω}
  {μ : Measure ℝ} {X : ι → Ω → ℝ} {r : ℝ}

/-- The coordinatewise spelling of the maximum of the family is its lattice supremum. -/
private theorem sup'_coord_eq (X : ι → Ω → ℝ) :
    (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => X i ω)
      = Finset.univ.sup' (Finset.univ_nonempty (α := ι)) X :=
  funext fun ω => (Finset.sup'_apply _ X ω).symm

/-- The coordinatewise spelling of the minimum of the family is its lattice infimum. -/
private theorem inf'_coord_eq (X : ι → Ω → ℝ) :
    (fun ω => Finset.univ.inf' Finset.univ_nonempty fun i => X i ω)
      = Finset.univ.inf' (Finset.univ_nonempty (α := ι)) X :=
  funext fun ω => (Finset.inf'_apply _ X ω).symm

/-- The maximum of an almost-everywhere measurable finite family is almost everywhere
measurable: `TauCeti.Finset.aemeasurable_sup'` in the coordinatewise spelling. -/
private theorem aemeasurable_max (hX : ∀ i, AEMeasurable (X i) P) :
    AEMeasurable (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) P := by
  rw [sup'_coord_eq]; exact TauCeti.Finset.aemeasurable_sup' _ fun i _ => hX i

/-- The minimum of an almost-everywhere measurable finite family is almost everywhere
measurable: `TauCeti.Finset.aemeasurable_inf'` in the coordinatewise spelling. -/
private theorem aemeasurable_min (hX : ∀ i, AEMeasurable (X i) P) :
    AEMeasurable (fun ω => Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) P := by
  rw [inf'_coord_eq]; exact TauCeti.Finset.aemeasurable_inf' _ fun i _ => hX i

/-- The maximum of a finite family is at most `x` exactly when every member is. -/
private theorem setOf_max_le (X : ι → Ω → ℝ) (x : ℝ) :
    {ω | (Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) ≤ x}
      = ⋂ i ∈ (Finset.univ : Finset ι), X i ⁻¹' Iic x := by
  ext ω
  simp [Finset.sup'_le_iff]

/-- The minimum of a finite family exceeds `x` exactly when every member does. -/
private theorem setOf_lt_min (X : ι → Ω → ℝ) (x : ℝ) :
    {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω}
      = ⋂ i ∈ (Finset.univ : Finset ι), X i ⁻¹' Ioi x := by
  ext ω
  simp [Finset.lt_inf'_iff]

/-- The maximum of an independent identically distributed finite family is at most `x` with
probability the `Fintype.card ι`-th power of the common lower-tail probability. -/
theorem measure_setOf_max_le_iid (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    P {ω | (Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) ≤ x}
      = μ (Iic x) ^ Fintype.card ι := by
  rw [setOf_max_le,
    hindep.measure_inter_preimage_eq_mul Finset.univ (sets := fun _ => Iic x)
      fun i _ => measurableSet_Iic]
  have h : ∀ i : ι, P (X i ⁻¹' Iic x) = μ (Iic x) := fun i =>
    (hlaw i).measure_eq (p := fun y => y ≤ x) measurableSet_Iic
  simp [h, Finset.card_univ]

/-- The minimum of an independent identically distributed finite family exceeds `x` with
probability the `Fintype.card ι`-th power of the common upper-tail probability. -/
theorem measure_setOf_lt_min_iid (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    P {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω}
      = μ (Ioi x) ^ Fintype.card ι := by
  rw [setOf_lt_min,
    hindep.measure_inter_preimage_eq_mul Finset.univ (sets := fun _ => Ioi x)
      fun i _ => measurableSet_Ioi]
  have h : ∀ i : ι, P (X i ⁻¹' Ioi x) = μ (Ioi x) := fun i =>
    (hlaw i).measure_eq (p := fun y => x < y) measurableSet_Ioi
  simp [h, Finset.card_univ]

/-- The real-valued form of `TauCeti.Probability.measure_setOf_max_le_iid`: the maximum of `d`
independent identically distributed variables has cumulative distribution function
`(cdf μ x) ^ d`. -/
theorem measureReal_setOf_max_le_iid [IsProbabilityMeasure μ] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    P.real {ω | (Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) ≤ x}
      = cdf μ x ^ Fintype.card ι := by
  rw [measureReal_def, measure_setOf_max_le_iid hindep hlaw x, ENNReal.toReal_pow,
    ← measureReal_def, ← cdf_eq_real]

/-- The real-valued form of `TauCeti.Probability.measure_setOf_lt_min_iid`: the minimum of `d`
independent identically distributed variables exceeds `x` with probability
`(1 - cdf μ x) ^ d`. -/
theorem measureReal_setOf_lt_min_iid [IsProbabilityMeasure μ] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    P.real {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω}
      = (1 - cdf μ x) ^ Fintype.card ι := by
  have _ : IsProbabilityMeasure P := (hlaw (Classical.arbitrary ι)).isProbabilityMeasure
  have htail : μ.real (Ioi x) = 1 - cdf μ x := by
    rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real]
  rw [measureReal_def, measure_setOf_lt_min_iid hindep hlaw x, ENNReal.toReal_pow,
    ← measureReal_def, htail]

/-- The minimum of `d` independent identically distributed variables has cumulative distribution
function `1 - (1 - cdf μ x) ^ d`. -/
theorem measureReal_setOf_min_le_iid [IsProbabilityMeasure μ] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    P.real {ω | (Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) ≤ x}
      = 1 - (1 - cdf μ x) ^ Fintype.card ι := by
  have _ : IsProbabilityMeasure P := (hlaw (Classical.arbitrary ι)).isProbabilityMeasure
  have hcompl : {ω | (Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) ≤ x}
      = {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω}ᶜ := by
    ext ω
    simp
  have hnull : NullMeasurableSet
      {ω | x < Finset.univ.inf' Finset.univ_nonempty fun i => X i ω} P :=
    (aemeasurable_min fun i => (hlaw i).aemeasurable).nullMeasurableSet_preimage measurableSet_Ioi
  rw [hcompl, measureReal_compl₀ hnull, probReal_univ,
    measureReal_setOf_lt_min_iid hindep hlaw x]

/-- The law of the maximum of `d` independent identically distributed variables, in cumulative
distribution function form. -/
theorem cdf_max_iid [IsProbabilityMeasure μ] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    cdf (P.map fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) x
      = cdf μ x ^ Fintype.card ι := by
  have hmax : AEMeasurable (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) P :=
    aemeasurable_max fun i => (hlaw i).aemeasurable
  have _ : IsProbabilityMeasure P := (hlaw (Classical.arbitrary ι)).isProbabilityMeasure
  rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hmax measurableSet_Iic,
    ← measureReal_setOf_max_le_iid hindep hlaw x]
  rfl

/-- The law of the minimum of `d` independent identically distributed variables, in cumulative
distribution function form. -/
theorem cdf_min_iid [IsProbabilityMeasure μ] (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (x : ℝ) :
    cdf (P.map fun ω => Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) x
      = 1 - (1 - cdf μ x) ^ Fintype.card ι := by
  have hmin : AEMeasurable (fun ω => Finset.univ.inf' Finset.univ_nonempty fun i => X i ω) P :=
    aemeasurable_min fun i => (hlaw i).aemeasurable
  have _ : IsProbabilityMeasure P := (hlaw (Classical.arbitrary ι)).isProbabilityMeasure
  rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hmin measurableSet_Iic,
    ← measureReal_setOf_min_le_iid hindep hlaw x]
  rfl

end Probability

end TauCeti
