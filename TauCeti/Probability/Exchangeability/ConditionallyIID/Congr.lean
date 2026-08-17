/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.Exchangeability.MixedIID.Congr

/-!
# Conditional i.i.d.-ness under almost-everywhere changes

`ConditionallyIIDWith μ X ν` constrains the joint law of `(ν, block)`, a `Measure.map` of `μ`
compared against a `Measure.bind` over `μ`. Both sides see `X` and `ν` only modulo `μ`-a.e.
equality, so the predicate transports along a coordinatewise a.e. change of the process and along
an a.e. change of the directing measure.

The directing-measure congruence is the one that matters in practice. A directing measure is only
ever determined a.e. — that is exactly what `conditionallyIID_ae_unique` says — so any construction
of one is free to be modified on a null set, and without this lemma a mathematically valid witness
becomes unusable at the interfaces that name it. Measurability is not an a.e. notion and is part of
the predicate, so it must be supplied afresh for the new witness.

The mixture-side analogues are in `MixedIID/Congr.lean` and the symmetry predicates are handled in
`Exchangeability/Congr.lean`.

## Main results

* `ConditionallyIIDWith.congr_process`, `ConditionallyIID.congr_process` — coordinatewise a.e. equal
  processes.
* `ConditionallyIIDWith.congr_directing` — an a.e. equal, measurable directing measure. A merely
  a.e. measurable replacement `ν'` is handled by applying it at `hν'.mk ν'`, with
  `hν'.measurable_mk` and `hνν'.trans hν'.ae_eq_mk`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Changing the process on a null set.** A directing measure for `X` is one for any
coordinatewise a.e. equal `Y`: the joint law of `(ν, block)` is unchanged. -/
theorem ConditionallyIIDWith.congr_process {μ : Measure Ω} {X Y : ι → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) (hXY : ∀ i, X i =ᵐ[μ] Y i) :
    ConditionallyIIDWith μ Y ν :=
  ConditionallyIIDWith.intro h.measurable_directing fun m k hk => by
    rw [← h.jointLaw_eq_disintegration k hk]
    refine Measure.map_congr ?_
    filter_upwards [ae_all_iff.2 fun i : Fin m => (hXY (k i)).symm] with ω hω
    exact Prod.ext rfl (funext hω)

/-- **Changing the process on a null set**, existential form. -/
theorem ConditionallyIID.congr_process {μ : Measure Ω} {X Y : ι → Ω → α}
    (h : ConditionallyIID μ X) (hXY : ∀ i, X i =ᵐ[μ] Y i) : ConditionallyIID μ Y :=
  let ⟨_, hν⟩ := h.exists_directing
  ConditionallyIID.of_directing (hν.congr_process hXY)

/-- **Changing the directing measure on a null set.** An a.e. equal random probability measure is
again a directing measure, provided it is measurable. Both sides of the defining identity move
together: the joint law changes only in its first coordinate, and the disintegration is a
`Measure.bind` over `μ`. -/
theorem ConditionallyIIDWith.congr_directing {μ : Measure Ω} {X : ι → Ω → α}
    {ν ν' : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν) (hν' : Measurable ν')
    (hνν' : ν =ᵐ[μ] ν') : ConditionallyIIDWith μ X ν' :=
  ConditionallyIIDWith.intro hν' fun m k hk =>
    calc μ.map (fun ω => (ν' ω, fun i : Fin m => X (k i) ω))
        = μ.map (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) :=
          Measure.map_congr (by filter_upwards [hνν'] with ω hω using Prod.ext hω.symm rfl)
      _ = μ.bind fun ω =>
            (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure :=
          h.jointLaw_eq_disintegration k hk
      _ = μ.bind fun ω =>
            (Measure.dirac (ν' ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν' ω).toMeasure :=
          Measure.bind_congr_right (by filter_upwards [hνν'] with ω hω using by rw [hω])

end Probability

end TauCeti
