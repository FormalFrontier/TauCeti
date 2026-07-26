/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.L2.Covariance
import TauCeti.Probability.Exchangeability.Map
import TauCeti.MeasureTheory.Function.BoundedMemLp

/-!
# Bounded observables of contractable processes in L²

This file supplies the bounded-observable entry point to the L² lane of the Exchangeability
roadmap.  Applying a measurable real-valued observable coordinatewise to a contractable process
preserves contractability, so whenever the mapped coordinates are square-integrable the process
inherits the uniform covariance structure of
`TauCeti.Probability.Exchangeability.L2.Covariance`: the means agree across all coordinates, so do
the variances, and every off-diagonal covariance takes a single common value.

* `Contractable.covariance_structure_comp` records this for any observable whose coordinates lie in
  L².
* `Contractable.covariance_structure_comp_of_bound` specializes it to a bounded observable, whose
  coordinates are square-integrable automatically on a finite measure space.

The bounded case discharges the worked-example check in `TauCetiRoadmap/Exchangeability/README.md`,
"In the real-valued L² lane, bounded observables give `MemLp 2` automatically."  Credit for the
reused material goes to the Tau Ceti covariance and map APIs; no material from
`cameronfreer/exchangeability` is used.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A measurable real-valued observable with square-integrable coordinates, applied coordinatewise
to a contractable process, gives uniform means, variances, and off-diagonal covariances: the means
agree across all coordinates, so do the variances, and every covariance of two distinct coordinates
takes the same value. -/
theorem Contractable.covariance_structure_comp {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_contractable : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) {f : α → ℝ}
    (hf : Measurable f) (hL2 : ∀ i, MemLp (fun ω => f (X i ω)) 2 μ) :
    (∀ i j, μ[fun ω => f (X i ω)] = μ[fun ω => f (X j ω)]) ∧
      (∀ i j, Var[fun ω => f (X i ω); μ] = Var[fun ω => f (X j ω); μ]) ∧
      (∀ i j k l, i ≠ j → k ≠ l →
        cov[fun ω => f (X i ω), fun ω => f (X j ω); μ] =
          cov[fun ω => f (X k ω), fun ω => f (X l ω); μ]) :=
  contractable_covariance_structure (hX_contractable.map_values hf hX_meas) hL2

/-- A bounded measurable real-valued observable of a contractable process has uniform means,
variances, and off-diagonal covariances.  On a finite measure space the square-integrability of the
mapped coordinates is automatic, so only an a.e. bound on each coordinate is required. -/
theorem Contractable.covariance_structure_comp_of_bound {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX_contractable : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    {f : α → ℝ} (hf : Measurable f) (C : ℝ) (hf_bound : ∀ i, ∀ᵐ ω ∂μ, |f (X i ω)| ≤ C) :
    (∀ i j, μ[fun ω => f (X i ω)] = μ[fun ω => f (X j ω)]) ∧
      (∀ i j, Var[fun ω => f (X i ω); μ] = Var[fun ω => f (X j ω); μ]) ∧
      (∀ i j k l, i ≠ j → k ≠ l →
        cov[fun ω => f (X i ω), fun ω => f (X j ω); μ] =
          cov[fun ω => f (X k ω), fun ω => f (X l ω); μ]) :=
  hX_contractable.covariance_structure_comp hX_meas hf fun i =>
    memLp_comp_of_bound hf (hX_meas i) C (by simpa only [Real.norm_eq_abs] using hf_bound i) 2

end Probability

end TauCeti
