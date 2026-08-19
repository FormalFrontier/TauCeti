/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.DeFinetti.DirectingMeasure.Basic
import TauCeti.Probability.DeFinetti.ViaL2.BlockFactorization
import TauCeti.Probability.DeFinetti.ConditionalCommonEnding
import TauCeti.Probability.DeFinetti.DirectingMeasure.BlockCylinder

/-!
# Conditional i.i.d.-ness of a contractable process, via `L²`

A contractable process on a standard Borel state space is conditionally i.i.d. with
`directingProbabilityMeasure μ X` as its directing measure:

```text
ConditionallyIIDWith μ X (directingProbabilityMeasure μ X).
```

This is where the `L²` route meets the common ending. `ViaL2/BlockFactorization.lean` supplies the
conditional factorization of an indicator block given `tailProcess X`, and
`conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral` asks for that identity
integrated over a directing-measure event. The integration itself is not done here: it is
`measure_inter_blockCylinder_eq_setLIntegral_of_condExp`, which takes the factorization as a
hypothesis and is shared with the martingale route. This file only supplies the `L²` factorization
to it, for an arbitrary strictly monotone selection.

The witness is preserved: the conclusion names `directingProbabilityMeasure μ X` itself rather
than asserting an unnamed existential.

Like the factorization it consumes, this file reaches conditional i.i.d.-ness without a reverse
martingale: neither `DeFinetti.BlockFactorization` nor `TailFactorization`, `JointRectangle`,
`DeFinetti.Theorem` or anything under `Probability.Martingale` is in its transitive imports. The
shared integration lemma is neutral for the same reason — it proves no factorization, only
consumes one.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 3** — the martingale-free
  standard-Borel de Finetti route, `deFinetti_viaL2`.
* The integration step is shared, not route-specific:
  `measure_inter_blockCylinder_eq_setLIntegral_of_condExp` in
  `DeFinetti/DirectingMeasure/BlockCylinder.lean` serves both this route and the prefix selection
  in `DeFinetti/JointRectangle.lean`.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal

namespace TauCeti

namespace Probability

namespace Contractable

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **A contractable process on a standard Borel space is conditionally i.i.d.**, with
`directingProbabilityMeasure μ X` as its directing measure.

This conditions on the directing measure itself. It does not assert conditional independence given
the whole of `tailProcess X`, which would additionally require identifying the σ-algebra generated
by `directingProbabilityMeasure μ X` with the tail. -/
theorem conditionallyIIDWith_directingProbabilityMeasure [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIIDWith μ X (directingProbabilityMeasure μ X) := by
  have hTail : tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
    tailProcess_le_ambient 0 fun c _ => hX_meas c
  refine conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral
    (fun n => (hX_meas n).aemeasurable) (measurable_directingProbabilityMeasure hTail) ?_
  intro r k hk S hS B hB
  -- The shared lemma states the right-hand side with `directingMeasure`; `hcore` asks for the
  -- bundled witness, and the two agree by `directingProbabilityMeasure_toMeasure`.
  simpa only [directingProbabilityMeasure_toMeasure] using
    measure_inter_blockCylinder_eq_setLIntegral_of_condExp hX_meas hB
      (hX.condExp_blockIndicatorProd_strictMono_tailProcess_ae_eq_prod_directingMeasure
        hX_meas hk hB) hS

end Contractable

end Probability

end TauCeti

end
