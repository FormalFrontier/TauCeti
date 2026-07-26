/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.MixedIID.Basic
-- Non-public: used only inside the proof below.
import TauCeti.Probability.Exchangeability.FiniteMarginals
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# The path law of a mixed i.i.d. process

A mixed i.i.d. process has, as its **path law**, a mixture of infinite product measures: for a
mixing representative `ν`,

```text
pathLaw μ X = ∫ P^{⊗ℕ} d(μ.map ν)(P)
```

written in the `Measure.bind` idiom.

## Main results

* `pathLaw_eq_bind_infinitePi_of_mixedIIDWith` — the representation, for an arbitrary mixing
  representative.

It needs only `[IsFiniteMeasure μ]`, a.e.-measurable coordinates, and the witness. In particular no
standard-Borel hypothesis appears: that is the cost of *supplying* a canonical witness, not of using
one, so this statement is about `MixedIIDWith` alone and carries no de Finetti dependency.

## Implementation

`MixedIIDWith` constrains only the *finite* blocks, so the work is the passage from finite blocks to
the whole path. The two sides are compared through their finite-dimensional prefix marginals via
`measure_eq_of_prefixProj_map_eq`: on the left `map_prefixProj_pathLaw` and the block identity, on
the right `map_bind` to push the marginal inside the mixture, `map_prefixProj_infinitePi_const` to
recognise each prefix marginal of an infinite power as the corresponding finite power, and
`bind_map` to re-index the mixture over `μ` rather than over `μ.map ν`.

This advances `TauCetiRoadmap/Exchangeability/README.md`, Layer 6, the directing-measure API bullet
asking for the mixture-of-product-measures form. That bullet also asks for `π` to be the *unique*
law of `ν`; uniqueness is not proved here or anywhere yet, and the roadmap name `deFinetti_mixture`
is reserved for the theorem that derives a canonical witness rather than assuming one.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The mixture representation of a path law.** If `ν` is a mixing representative for `X`, the
path law of `X` is the `μ.map ν`-mixture of the infinite product measures `P^{⊗ℕ}`. -/
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
