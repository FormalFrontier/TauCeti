/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.MixedIID.Basic
public import TauCeti.Probability.Exchangeability.FiniteMarginals
-- Non-public: the Giry interchange laws and the product-kernel adapters are used only in proofs.
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# The de Finetti mixture representation

A mixed i.i.d. process has, as its **path law**, a mixture of infinite product measures: for a
mixing representative `ν`,

```text
pathLaw μ X = ∫ P^{⊗ℕ} d(μ.map ν)(P)
```

written in the `Measure.bind` idiom. `MixedIIDWith` constrains only the *finite* blocks, so the
content here is the passage from finite blocks to the whole path — carried by finite-dimensional
marginal uniqueness on one side and the projective-limit property of `Measure.infinitePi` on the
other.

## Main results

* `pathLaw_eq_bind_infinitePi_of_mixedIIDWith` — the mixture representation, for an arbitrary
  mixing representative.

The statement assumes only `[IsFiniteMeasure μ]`, a.e.-measurable coordinates, and the witness: no
standard-Borel hypothesis appears, since none is needed once a witness is given. Supplying the
*canonical* witness is what needs standard Borel, and that lives with the summit theorems.

This advances `TauCetiRoadmap/Exchangeability/README.md`, Layer 6, the directing-measure API bullet
asking for the mixture-of-product-measures form. The roadmap's `deFinetti_mixture` is reserved for
the eventual theorem that *derives* the canonical witness rather than assuming one.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The de Finetti mixture representation.** If `ν` is a mixing representative for `X`, the path
law of `X` is the `μ.map ν`-mixture of the infinite product measures `P^{⊗ℕ}`.

`MixedIIDWith` gives the finite-block laws; this upgrades them to the whole path law. Both sides are
compared through their finite-dimensional prefix marginals, where the block identity meets the
projective-limit property of `Measure.infinitePi`. -/
theorem pathLaw_eq_bind_infinitePi_of_mixedIIDWith {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : ∀ n, AEMeasurable (X n) μ) {ν : Ω → ProbabilityMeasure α}
    (h : MixedIIDWith μ X ν) :
    pathLaw μ X = (μ.map ν).bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
  have hΦ : AEMeasurable (fun ω => fun i => X i ω : Ω → ℕ → α) μ := aemeasurable_pi_lambda _ hX
  have hν : AEMeasurable ν μ := h.measurable_mixingRepresentative.aemeasurable
  have hpow : AEMeasurable (fun P : ProbabilityMeasure α =>
      Measure.infinitePi fun _ : ℕ => (P : Measure α)) (μ.map ν) :=
    TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable
  haveI : IsFiniteMeasure (pathLaw μ X) := by rw [pathLaw_def]; infer_instance
  refine measure_eq_of_prefixProj_map_eq fun n => ?_
  have hfin : AEMeasurable (fun P : ProbabilityMeasure α =>
      (ProbabilityMeasure.pi fun _ : Fin n => P).toMeasure) (μ.map ν) :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_pi_const_toMeasure
      (fun P : ProbabilityMeasure α => P) measurable_id).aemeasurable
  -- the prefix marginal of each infinite power is the corresponding finite power
  have hstep : ∀ P : ProbabilityMeasure α,
      (Measure.infinitePi fun _ : ℕ => (P : Measure α)).map (prefixProj α n)
        = (ProbabilityMeasure.pi fun _ : Fin n => P).toMeasure := by
    intro P
    have hp : prefixProj α n = fun x : ℕ → α => fun i : Fin n => x i := rfl
    rw [hp, ProbabilityMeasure.toMeasure_pi,
      TauCeti.MeasureTheory.map_prefixProj_infinitePi_const P n]
  calc (pathLaw μ X).map (prefixProj α n)
      = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin n => ν ω).toMeasure := by
        rw [map_prefixProj_pathLaw μ hΦ n, prefixLaw_def,
          h.blockLaw_eq_mixture _ Fin.val_injective]
    _ = ((μ.map ν).bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)).map
          (prefixProj α n) := by
        rw [TauCeti.MeasureTheory.map_bind hpow (measurable_prefixProj n)]
        simp_rw [hstep]
        rw [TauCeti.MeasureTheory.bind_map hν hfin]
        rfl

end Probability

end TauCeti
