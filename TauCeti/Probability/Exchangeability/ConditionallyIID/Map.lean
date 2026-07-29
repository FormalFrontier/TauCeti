/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# Transferring conditional i.i.d.-ness along the path map

The canonical process on path space carries `ConditionallyIID` back to the original process.

## Main results

* `conditionallyIID_of_conditionallyIID_pathLaw` — if the coordinate process is conditionally
  i.i.d. under `pathLaw μ X`, then `X` is conditionally i.i.d. under `μ`.

## Implementation

This is the conditional counterpart of `mixedIID_of_mixedIID_pathLaw`, and the roadmap refers to it
as `conditionallyIID_transfer`. Both sides of the disintegration identity move along the path map
`φ ω = fun i => X i ω`: the joint law by `Measure.map_map`, and the mixture by `bind_map`. The
directing measure transfers as `ν ∘ φ`.

Its purpose is to remove `[StandardBorelSpace Ω]` from statements proved on path space, which is
standard Borel whenever the state space is.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Path-law transfer for the conditional predicate.** If the coordinate process is conditionally
i.i.d. under the path law of `X`, then `X` itself is conditionally i.i.d., with directing measure
the path-space one composed with `ω ↦ fun i => X i ω`.

The roadmap names this `conditionallyIID_transfer`; the name here matches its mixture counterpart
`mixedIID_of_mixedIID_pathLaw`. -/
theorem conditionallyIID_of_conditionallyIID_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n))
    (h : ConditionallyIID (pathLaw μ X) fun n p => p n) :
    ConditionallyIID μ X := by
  obtain ⟨ν, hν⟩ := h.exists_directing
  have hφ : Measurable (fun ω => fun i => X i ω : Ω → ℕ → α) := measurable_pi_lambda _ hX_meas
  have hνm : Measurable ν := hν.measurable_directing
  refine ConditionallyIID.of_directing (ConditionallyIIDWith.intro (hνm.comp hφ) ?_)
  intro m k hk
  have hcoord : Measurable (fun p : ℕ → α => fun i : Fin m => p (k i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (k i)
  have houter : Measurable (fun p : ℕ → α => (ν p, fun i : Fin m => p (k i))) :=
    hνm.prodMk hcoord
  have hker : Measurable (fun p : ℕ → α =>
      (Measure.dirac (ν p)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν p).toMeasure) :=
    TauCeti.MeasureTheory.measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure ν hνm
  calc μ.map (fun ω => (ν (fun i => X i ω), fun i : Fin m => X (k i) ω))
      = (pathLaw μ X).map (fun p => (ν p, fun i : Fin m => p (k i))) := by
        rw [pathLaw_def, Measure.map_map houter hφ]
        rfl
    _ = (pathLaw μ X).bind fun p =>
          (Measure.dirac (ν p)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν p).toMeasure :=
        hν.jointLaw_eq_disintegration k hk
    _ = μ.bind fun ω =>
          (Measure.dirac (ν fun i => X i ω)).prod
            (ProbabilityMeasure.pi fun _ : Fin m => ν fun i => X i ω).toMeasure := by
        rw [pathLaw_def]
        exact TauCeti.MeasureTheory.bind_map hφ.aemeasurable hker.aemeasurable

end Probability

end TauCeti
