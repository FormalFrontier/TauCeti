/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.MixedIID.Basic
public import TauCeti.Probability.Exchangeability.Congr

/-!
# Mixed i.i.d.-ness under almost-everywhere changes

`MixedIIDWith μ X ν` is a family of identities between measures built from `X` and `ν` by
`Measure.map` and `Measure.bind`, so it sees both arguments only modulo `μ`-a.e. equality. This file
records the two resulting congruences: the process may be changed coordinatewise a.e., and the
mixing representative may be changed a.e. — the latter subject to the measurability the definition
builds in, which is not itself an a.e. notion and so must be supplied for the new witness.

Together these make the predicate usable after the routine null-set surgery that produces, say, a
measurable version of an a.e. measurable coordinate. The conditional analogues are in
`ConditionallyIID/Congr.lean`, and the symmetry predicates are handled in
`Exchangeability/Congr.lean`.

## Main results

* `MixedIIDWith.congr_process`, `MixedIID.congr_process` — coordinatewise a.e. equal processes.
* `MixedIIDWith.congr_mixingRepresentative` — an a.e. equal, measurable mixing representative. A
  merely a.e. measurable replacement `ν'` is handled by applying it at `hν'.mk ν'`, with
  `hν'.measurable_mk` and `hνν'.trans hν'.ae_eq_mk`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Changing the process on a null set.** A mixing representative for `X` is one for any
coordinatewise a.e. equal `Y`: the block laws the definition constrains are unchanged. -/
theorem MixedIIDWith.congr_process {μ : Measure Ω} {X Y : ι → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν) (hXY : ∀ i, X i =ᵐ[μ] Y i) :
    MixedIIDWith μ Y ν :=
  MixedIIDWith.intro h.measurable_mixingRepresentative fun m k hk => by
    rw [← blockLaw_congr hXY k]
    exact h.blockLaw_eq_mixture k hk

/-- **Changing the process on a null set**, existential form. -/
theorem MixedIID.congr_process {μ : Measure Ω} {X Y : ι → Ω → α} (h : MixedIID μ X)
    (hXY : ∀ i, X i =ᵐ[μ] Y i) : MixedIID μ Y :=
  let ⟨_, hν⟩ := h.exists_mixingRepresentative
  MixedIID.of_mixingRepresentative (hν.congr_process hXY)

/-- **Changing the mixing representative on a null set.** An a.e. equal random probability measure
is again a mixing representative, provided it is measurable: the mixture side of the defining
identity is a `Measure.bind` over `μ`, which only sees `ν` a.e., but measurability of the witness is
part of the predicate and is not an a.e. notion. -/
theorem MixedIIDWith.congr_mixingRepresentative {μ : Measure Ω} {X : ι → Ω → α}
    {ν ν' : Ω → ProbabilityMeasure α} (h : MixedIIDWith μ X ν) (hν' : Measurable ν')
    (hνν' : ν =ᵐ[μ] ν') : MixedIIDWith μ X ν' :=
  MixedIIDWith.intro hν' fun m k hk => by
    rw [h.blockLaw_eq_mixture k hk]
    exact Measure.bind_congr_right (by filter_upwards [hνν'] with ω hω using by rw [hω])

end Probability

end TauCeti
