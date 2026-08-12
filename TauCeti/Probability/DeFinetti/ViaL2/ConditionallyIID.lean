/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.DeFinetti.DirectingMeasure.Basic
public import TauCeti.Probability.Exchangeability.Basic
import TauCeti.Probability.DeFinetti.ViaL2.BlockFactorization
import TauCeti.Probability.DeFinetti.ConditionalCommonEnding
import TauCeti.Probability.DeFinetti.DirectingMeasure.Integral

/-!
# Conditional i.i.d.-ness of a contractable process, via `L²`

A contractable process on a standard Borel state space is conditionally i.i.d. given its tail, with
the directing measure as witness:

```text
ConditionallyIIDWith μ X (directingProbabilityMeasure μ X).
```

This is the integration step of the `L²` route. `ViaL2/BlockFactorization.lean` supplies the
conditional factorization of an indicator block given `tailProcess X`, and
`conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral` asks for exactly that
identity integrated over a directing-measure event. Such an event is tail-measurable, so
integrating the factorization over it is `setIntegral_condExp`, and the block cylinder's measure
is the integral of its indicator.

The witness is preserved: the conclusion names `directingProbabilityMeasure μ X` itself rather
than asserting an unnamed existential.

The arithmetic stays in `ℝ` — every factor is a probability of a set and the process measure is
finite — so `ℝ≥0∞` enters only at the boundary, in the single appeal to
`ofReal_integral_eq_lintegral_prod_directingMeasure`.

Like the factorization it consumes, this file reaches conditional i.i.d.-ness without a reverse
martingale: neither `DeFinetti.BlockFactorization` nor `TailFactorization`, `JointRectangle`,
`DeFinetti.Theorem` or anything under `Probability.Martingale` is in its transitive imports.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 3** — the martingale-free
  standard-Borel de Finetti route, `deFinetti_viaL2`.
* The integration argument follows the private `measure_inter_blockCylinder_eq_setLIntegral` in
  `DeFinetti/JointRectangle.lean`, which performs the same steps for the martingale route: test the
  factorization against the tail event with `setIntegral_condExp`, read the cylinder's mass as the
  integral of its indicator, and convert once at the `ℝ≥0∞` boundary. The only substantive
  difference is which factorization is fed in — here the strictly monotone form from
  `ViaL2/BlockFactorization.lean` rather than the prefix form. This file does not import that
  module; the debt is to its proof plan, not to its code.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal

namespace TauCeti

namespace Probability

namespace Contractable

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **A contractable process on a standard Borel space is conditionally i.i.d. given its tail**,
with the directing measure as the witness. -/
theorem conditionallyIIDWith_directingProbabilityMeasure [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIIDWith μ X (directingProbabilityMeasure μ X) := by
  classical
  have hTail : tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
    tailProcess_le_ambient 0 fun c _ => hX_meas c
  refine conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral
    (fun n => (hX_meas n).aemeasurable) (measurable_directingProbabilityMeasure hTail) ?_
  intro r k hk S hS B hB
  set A : Set Ω := directingProbabilityMeasure μ X ⁻¹' S with hA
  set W : Ω → ℝ := fun ω => ∏ i, (directingMeasure μ X ω).real (B i) with hW
  -- `A` is a tail event, being a preimage under the tail-measurable directing measure.
  have hA_tail : MeasurableSet[tailProcess X] A :=
    measurable_tailProcess_directingProbabilityMeasure hS
  have hA_meas : MeasurableSet A := hTail _ hA_tail
  have hW_int : Integrable W μ := integrable_prod_directingMeasure_real hTail hB
  have hC_meas : MeasurableSet (blockCylinder X k B) :=
    measurableSet_blockCylinder (fun i => hX_meas (k i)) hB
  have hZ_int : Integrable (blockIndicatorProd X k B) μ :=
    integrable_blockIndicatorProd (fun i => (hX_meas (k i)).aemeasurable) hB
  -- The cylinder's measure is the integral of its indicator over `A`.
  have hLHS : ∫ ω in A, blockIndicatorProd X k B ω ∂μ = (μ (A ∩ blockCylinder X k B)).toReal := by
    -- `blockIndicatorProd_apply` is `@[simp]`, so anchor the indicator form first.
    rw [blockIndicatorProd_eq_indicator]
    simp [integral_indicator hC_meas, Measure.restrict_apply hC_meas, Set.inter_comm,
      measureReal_def]
  -- Integrating the factorization over the tail event `A`.
  have hmid : ∫ ω in A, blockIndicatorProd X k B ω ∂μ = ∫ ω in A, W ω ∂μ := by
    rw [← setIntegral_condExp hTail hZ_int hA_tail]
    have hfac := hX.condExp_blockIndicatorProd_strictMono_tailProcess_ae_eq_prod_directingMeasure
      hX_meas hk hB
    exact setIntegral_congr_ae hA_meas (hfac.mono fun ω hω _ => hω)
  calc μ (A ∩ blockCylinder X k B)
      = ENNReal.ofReal ((μ (A ∩ blockCylinder X k B)).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = ENNReal.ofReal (∫ ω in A, W ω ∂μ) := by rw [← hLHS, hmid]
    _ = ∫⁻ ω in A, ∏ i, directingMeasure μ X ω (B i) ∂μ :=
        ofReal_integral_eq_lintegral_prod_directingMeasure hW_int.restrict
    _ = ∫⁻ ω in A, ∏ i, (directingProbabilityMeasure μ X ω : Measure α) (B i) ∂μ := by
        simp only [directingProbabilityMeasure_toMeasure]

end Contractable

end Probability

end TauCeti

end
