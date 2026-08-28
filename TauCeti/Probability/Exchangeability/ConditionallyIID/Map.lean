/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
import TauCeti.MeasureTheory.Measure.GiryMonad
-- Non-public: the Giry-measurability of a pushforward is used only inside the proofs below.
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Maps of conditionally i.i.d. families

Two ways of moving `ConditionallyIID` along a map. Applying a measurable map to the *values* of
every coordinate gives another conditionally i.i.d. family, whose directing measure is the
pushforward of the original one; and the canonical process on path space carries
`ConditionallyIID` back to the original process.

## Main results

* `ConditionallyIIDWith.map_values` — the coordinatewise value pushforward, at a named directing
  measure, together with its existential corollary `ConditionallyIID.map_values`.
* `ConditionallyIIDWith.of_pathLaw` — the transfer at a named directing measure, identifying the
  transferred witness as `ν ∘ (ω ↦ fun i => X i ω)`.
* `conditionallyIID_of_conditionallyIID_pathLaw` — its existential corollary.

## Implementation

These are the conditional counterparts of `MixedIIDWith.map_values` and
`mixedIID_of_mixedIID_pathLaw`; the roadmap refers to the second as `conditionallyIID_transfer`,
and asks for the first as the closure of each symmetry class under a coordinatewise pushforward
(`TauCetiRoadmap/Exchangeability/README.md`, Layer 0). Where the mixture predicate needs only the
block identity to move, the conditional predicate carries the directing measure along as a
coordinate of a joint law, so `map_values` transports the *whole* disintegration identity along
`(Q, x) ↦ (Q.map f, f ∘ x)`. That map splits as a product, which is what lets
`Measure.map_prod_map` reduce the mixture side to `Measure.map_dirac'` on the tag and
`Measure.pi_map_pi` on the sampled block.

Both sides of the path-law transfer move along the path map `φ ω = fun i => X i ω`: the joint law
by `Measure.map_map`, and the mixture by `bind_map`. The directing measure transfers as `ν ∘ φ`.
Its purpose is to remove `[StandardBorelSpace Ω]` from statements proved on path space, which is
standard Borel whenever the state space is.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

/-- **Conditional i.i.d.-ness is preserved by a coordinatewise measurable map of the value
space**, at a named directing measure: if `X` is conditionally i.i.d. with directing measure `ν`,
then `fun i ω => f (X i ω)` is conditionally i.i.d. with directing measure the pushforward
`fun ω => (ν ω).map f`.

Unlike its mixture counterpart `MixedIIDWith.map_values`, this moves the joint law of the directing
measure and a block, so the transported map acts on the tag as well: it is
`(Q, x) ↦ (Q.map f, f ∘ x)`. -/
theorem ConditionallyIIDWith.map_values {μ : Measure Ω} {X : ι → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν)
    {f : α → β} (hf : Measurable f) :
    ConditionallyIIDWith μ (fun i ω => f (X i ω)) fun ω => (ν ω).map hf.aemeasurable := by
  have hmapQ : Measurable fun Q : ProbabilityMeasure α => Q.map hf.aemeasurable :=
    TauCeti.MeasureTheory.measurable_probabilityMeasure_map hf
  refine ConditionallyIIDWith.intro (hmapQ.comp h.measurable_directing) fun m k hk => ?_
  set F : (Fin m → α) → Fin m → β := fun x i => f (x i) with hF
  have hFmeas : Measurable F := measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
  have hΦ : Measurable
      (Prod.map (fun Q : ProbabilityMeasure α => Q.map hf.aemeasurable) F) :=
    hmapQ.prodMap hFmeas
  have hinner : AEMeasurable (fun ω => (ν ω, fun i : Fin m => X (k i) ω)) μ :=
    h.measurable_directing.aemeasurable.prodMk
      (aemeasurable_pi_lambda _ fun i => h.aemeasurable (k i))
  have hK : AEMeasurable (fun ω =>
      (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure) μ :=
    (TauCeti.MeasureTheory.measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure ν
      h.measurable_directing).aemeasurable
  calc μ.map (fun ω => ((ν ω).map hf.aemeasurable, fun i : Fin m => f (X (k i) ω)))
      = (μ.map fun ω => (ν ω, fun i : Fin m => X (k i) ω)).map
          (Prod.map (fun Q : ProbabilityMeasure α => Q.map hf.aemeasurable) F) := by
        rw [AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hinner]
        exact congrArg (μ.map ·) (funext fun ω => by simp [hF, Prod.map])
    _ = (μ.bind fun ω => (Measure.dirac (ν ω)).prod
          (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure).map
          (Prod.map (fun Q : ProbabilityMeasure α => Q.map hf.aemeasurable) F) := by
        rw [h.jointLaw_eq_disintegration k hk]
    _ = μ.bind fun ω => ((Measure.dirac (ν ω)).prod
          (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure).map
          (Prod.map (fun Q : ProbabilityMeasure α => Q.map hf.aemeasurable) F) :=
        TauCeti.MeasureTheory.map_bind hK hΦ
    _ = μ.bind fun ω => (Measure.dirac ((ν ω).map hf.aemeasurable)).prod
          (ProbabilityMeasure.pi fun _ : Fin m => (ν ω).map hf.aemeasurable).toMeasure := by
        refine congrArg (μ.bind ·) (funext fun ω => ?_)
        have : IsProbabilityMeasure ((ν ω : Measure α).map f) :=
          (ν ω : Measure α).isProbabilityMeasure_map hf.aemeasurable
        simp only [ProbabilityMeasure.toMeasure_pi, ProbabilityMeasure.toMeasure_map]
        rw [← Measure.map_dirac' hmapQ (ν ω),
          ← Measure.pi_map_pi (f := fun _ : Fin m => f) fun _ => hf.aemeasurable]
        exact (Measure.map_prod_map _ _ hmapQ hFmeas).symm

/-- **Conditional i.i.d.-ness is preserved by a coordinatewise measurable map of the value
space.** -/
theorem ConditionallyIID.map_values {μ : Measure Ω} {X : ι → Ω → α}
    (h : ConditionallyIID μ X) {f : α → β} (hf : Measurable f) :
    ConditionallyIID μ fun i ω => f (X i ω) :=
  let ⟨_, hν⟩ := h.exists_directing
  ConditionallyIID.of_directing (hν.map_values hf)

/-- **Path-law transfer, at a named directing measure.** If the coordinate process is conditionally
i.i.d. under the path law of `X` with directing measure `ν`, then `X` is conditionally i.i.d. with
directing measure `ν ∘ (ω ↦ fun i => X i ω)`.

Both sides of the disintegration identity move along the path map: the joint law by
`Measure.map_map`, the mixture by `bind_map`. -/
theorem ConditionallyIIDWith.of_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n)) {ν : (ℕ → α) → ProbabilityMeasure α}
    (hν : ConditionallyIIDWith (pathLaw μ X) (fun n p => p n) ν) :
    ConditionallyIIDWith μ X fun ω => ν fun i => X i ω := by
  have hφ : Measurable (fun ω => fun i => X i ω : Ω → ℕ → α) := measurable_pi_lambda _ hX_meas
  have hνm : Measurable ν := hν.measurable_directing
  refine ConditionallyIIDWith.intro (hνm.comp hφ) ?_
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

/-- **Path-law transfer for the conditional predicate**, existential form. The roadmap names this
`conditionallyIID_transfer`; the name here matches its mixture counterpart
`mixedIID_of_mixedIID_pathLaw`. -/
theorem conditionallyIID_of_conditionallyIID_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n))
    (h : ConditionallyIID (pathLaw μ X) fun n p => p n) :
    ConditionallyIID μ X :=
  let ⟨_, hν⟩ := h.exists_directing
  ConditionallyIID.of_directing (hν.of_pathLaw hX_meas)


end Probability

end TauCeti
