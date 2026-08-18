/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Pi

/-!
# A finite product of weighted measures is the product measure with the product weight

`MeasureTheory.Measure.pi (fun i => (μ i).withDensity (f i))` is
`(MeasureTheory.Measure.pi μ).withDensity (fun x => ∏ i, f i (x i))`: putting a density on each
factor of a finite product measure is the same as putting the product of the densities on the
product measure.

Mathlib has the two-factor versions `MeasureTheory.Measure.prod_withDensity₀` and
`MeasureTheory.Measure.prod_withDensity` but not the `MeasureTheory.Measure.pi` version, which is
what a coordinatewise weight on `ℝ^ι` needs. The motivating instance is the multivariate Gaussian,
whose product measure is Lebesgue measure on `ℝ^ι` weighted by the product of the one-dimensional
Gaussian densities.

The proof identifies the two measures on measurable boxes via `MeasureTheory.Measure.pi_eq`; the
box computation is `TauCeti.lintegral_fintype_prod_eq_prod₀` applied to the
indicator-truncated densities.

## Main statements

* `TauCeti.pi_withDensity₀`: the identification, for almost everywhere measurable densities.
* `TauCeti.pi_withDensity`: the same for measurable densities.
-/

public section

open MeasureTheory MeasureTheory.Measure

open scoped ENNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι] {α : ι → Type*} {mα : ∀ i, MeasurableSpace (α i)}

/-- **Coordinatewise densities multiply.** For a finite family of σ-finite measures `μ i` and
almost everywhere measurable densities `f i`, the product of the weighted measures
`(μ i).withDensity (f i)` is the product measure weighted by the product density
`x ↦ ∏ i, f i (x i)`.

The σ-finiteness assumption on the weighted factors is what `MeasureTheory.Measure.pi_eq` needs to
recognize the left-hand side as *the* product measure; it is automatic when the weighted factors
are finite (as for probability densities). -/
theorem pi_withDensity₀ (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] {f : ∀ i, α i → ℝ≥0∞}
    (hf : ∀ i, AEMeasurable (f i) (μ i)) [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i))
      = (Measure.pi μ).withDensity fun x => ∏ i, f i (x i) := by
  refine Measure.pi_eq fun s hs => ?_
  -- On a measurable box the product density truncates coordinatewise.
  have hbox : ∀ x : ∀ i, α i, (Set.pi Set.univ s).indicator (fun x => ∏ i, f i (x i)) x
      = ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (Set.mem_univ_pi.1 hx i) (f i)).symm
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ := not_forall.1 fun h => hx (Set.mem_univ_pi.2 h)
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi (f i))).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs), lintegral_congr hbox,
    lintegral_fintype_prod_eq_prod₀ μ fun i => (hf i).indicator (hs i)]
  exact Finset.prod_congr rfl fun i _ => by
    rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]

/-- **Coordinatewise densities multiply**, for measurable densities; see
`TauCeti.pi_withDensity₀` for the almost everywhere measurable version. -/
theorem pi_withDensity (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] {f : ∀ i, α i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i))
      = (Measure.pi μ).withDensity fun x => ∏ i, f i (x i) :=
  pi_withDensity₀ μ fun i => (hf i).aemeasurable

end TauCeti
