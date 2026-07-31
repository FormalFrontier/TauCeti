/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.Exchangeability.FiniteMarginals
import TauCeti.MeasureTheory.Measure.ProductKernel
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# The full-path joint disintegration

`ConditionallyIIDWith μ X ν` constrains the joint law of `(ν, block)` along each *finite* selection
of coordinates. This file upgrades that to the whole path at once: the joint law of the directing
measure together with the entire process is the disintegration `∫ δ_{ν ω} ⊗ (ν ω)^{⊗ℕ} dμ(ω)`.

## Main results

* `TauCeti.Probability.ConditionallyIIDWith.jointPathLaw_eq_pathDisintegration`

## Implementation

Both measures live on `ProbabilityMeasure α × (ℕ → α)`, and they agree on every finite prefix: the
joint law by the defining identity at the selection `Fin n → ℕ`, the disintegration by projecting
each fibre `δ_Q ⊗ Q^{⊗ℕ}` through `map_prefixProj_infinitePi_const`. Extensionality then comes from
`ext_of_generate_finite` against the π-system `prefixSets` of preimages under the prefix maps
`prefixPair`:

* it is a π-system because two such sets can be re-presented at the longer of their two prefixes
  (`prefixPair_comp`);
* it generates the product σ-algebra, the first factor read off the empty prefix and the path factor
  through `MeasurableSpace.comap_iSup` on the coordinate evaluations.

Mathlib's `IsProjectiveLimit` is stated for pure dependent products `∀ i, α i`, so it does not apply
to this product directly; the π-system argument avoids reindexing the pair through `Option ℕ`.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 6 (directing measures) — the
  path-level form of the conditional disintegration the directing-measure layer is stated against.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles* (Springer, 2005), §1.1, where
  the conditional predicate is stated blockwise.

The path-level form is what downstream work consumes — empirical measures as objects, the
affine/barycenter representation, and ergodic decomposition all read the joint law of `(ν, X)` in
one piece rather than block by block.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}

/-- The joint path law: the law of the directing measure together with the whole path.

`@[expose]` is load-bearing: `jointPathLaw_def` below is the definitional unfolding, and under the
module system an exported theorem may only unfold exposed definitions. Unlike `blockLaw`, writing
the proof as `(rfl)` does not discharge it here. -/
@[expose]
def jointPathLaw (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    Measure (ProbabilityMeasure α × (ℕ → α)) :=
  μ.map fun ω => (ν ω, fun i => X i ω)

/-- The full-path disintegration measure `∫ δ_{ν ω} ⊗ (ν ω)^{⊗ℕ} dμ(ω)`. Exposed for the same
reason as `jointPathLaw`. -/
@[expose]
def pathDisintegration (μ : Measure Ω) (ν : Ω → ProbabilityMeasure α) :
    Measure (ProbabilityMeasure α × (ℕ → α)) :=
  μ.bind fun ω =>
    (Measure.dirac (ν ω)).prod (Measure.infinitePi fun _ : ℕ => (ν ω : Measure α))

theorem jointPathLaw_def (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    jointPathLaw μ X ν = μ.map fun ω => (ν ω, fun i => X i ω) := rfl

theorem pathDisintegration_def (μ : Measure Ω) (ν : Ω → ProbabilityMeasure α) :
    pathDisintegration μ ν = μ.bind fun ω =>
      (Measure.dirac (ν ω)).prod (Measure.infinitePi fun _ : ℕ => (ν ω : Measure α)) := rfl

/-- The prefix pushforward of the joint path law is the joint block law of the first `n`
coordinates. -/
theorem map_prefixPair_jointPathLaw (hX : ∀ i, Measurable (X i)) (hν : Measurable ν) (n : ℕ) :
    (jointPathLaw μ X ν).map (prefixPair (ProbabilityMeasure α) α n)
      = μ.map fun ω => (ν ω, fun i : Fin n => X i ω) := by
  have hpath : Measurable (fun ω => (ν ω, fun i => X i ω) :
      Ω → ProbabilityMeasure α × (ℕ → α)) :=
    hν.prodMk (measurable_pi_lambda _ hX)
  rw [jointPathLaw_def, Measure.map_map (measurable_prefixPair (ProbabilityMeasure α) α n) hpath]
  simp only [Function.comp_def, prefixPair_apply]

/-- The prefix pushforward of the joint path law is the block-level disintegration, by the defining
identity at the first `n` coordinates. -/
theorem map_prefixPair_jointPathLaw_eq (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, Measurable (X i))
    (n : ℕ) :
    (jointPathLaw μ X ν).map (prefixPair (ProbabilityMeasure α) α n)
      = μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin n => ν ω).toMeasure := by
  rw [map_prefixPair_jointPathLaw hX h.measurable_directing n]
  exact h.jointLaw_eq_disintegration (fun i : Fin n => (i : ℕ)) Fin.val_injective

/-- The prefix pushforward of the full-path disintegration is the block-level disintegration:
projecting `δ_{ν ω} ⊗ (ν ω)^{⊗ℕ}` onto the first `n` path coordinates leaves
`δ_{ν ω} ⊗ (ν ω)^{⊗ Fin n}`. -/
theorem map_prefixPair_pathDisintegration (hν : Measurable ν) (n : ℕ) :
    (pathDisintegration μ ν).map (prefixPair (ProbabilityMeasure α) α n)
      = μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin n => ν ω).toMeasure := by
  have hker : Measurable (fun ω =>
      (Measure.dirac (ν ω)).prod (Measure.infinitePi fun _ : ℕ => (ν ω : Measure α))) :=
    (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const (ι' := ℕ)
      (id : ProbabilityMeasure α → ProbabilityMeasure α) measurable_id).comp hν
  -- Projecting one fibre `δ_Q ⊗ Q^{⊗ℕ}` onto the first `n` path coordinates.
  have hfibre : ∀ Q : ProbabilityMeasure α,
      ((Measure.dirac Q).prod (Measure.infinitePi fun _ : ℕ => (Q : Measure α))).map
          (prefixPair (ProbabilityMeasure α) α n)
        = (Measure.dirac Q).prod (ProbabilityMeasure.pi fun _ : Fin n => Q).toMeasure := by
    intro Q
    have hpref : Measurable (fun x : ℕ → α => fun i : Fin n => x (i : ℕ)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
    calc ((Measure.dirac Q).prod (Measure.infinitePi fun _ : ℕ => (Q : Measure α))).map
            (prefixPair (ProbabilityMeasure α) α n)
        = ((Measure.dirac Q).map id).prod
            ((Measure.infinitePi fun _ : ℕ => (Q : Measure α)).map
              fun x : ℕ → α => fun i : Fin n => x (i : ℕ)) := by
          rw [Measure.map_prod_map _ _ measurable_id hpref]
          congr 1
          funext q
          simp [prefixPair_apply, Prod.map]
      _ = (Measure.dirac Q).prod (ProbabilityMeasure.pi fun _ : Fin n => Q).toMeasure := by
          rw [Measure.map_id, TauCeti.MeasureTheory.map_prefixProj_infinitePi_const Q n,
            ProbabilityMeasure.toMeasure_pi]
  rw [pathDisintegration_def,
    TauCeti.MeasureTheory.map_bind hker.aemeasurable
      (measurable_prefixPair (ProbabilityMeasure α) α n)]
  congr 1
  funext ω
  exact hfibre (ν ω)

/-! ### The full-path disintegration -/

/-- **The full-path joint disintegration.** For a conditionally i.i.d. process the joint law of the
directing measure together with the *whole* path is the disintegration
`∫ δ_{ν ω} ⊗ (ν ω)^{⊗ℕ} dμ(ω)`.

The definition of `ConditionallyIIDWith` gives this along each finite selection of coordinates; this
upgrades it to the entire path at once. -/
theorem ConditionallyIIDWith.jointPathLaw_eq_pathDisintegration [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, Measurable (X i)) :
    jointPathLaw μ X ν = pathDisintegration μ ν := by
  have hpath : Measurable (fun ω => (ν ω, fun i => X i ω) :
      Ω → ProbabilityMeasure α × (ℕ → α)) :=
    h.measurable_directing.prodMk (measurable_pi_lambda _ hX)
  haveI : IsFiniteMeasure (jointPathLaw μ X ν) := by
    rw [jointPathLaw_def]; exact Measure.isFiniteMeasure_map _ _
  refine measure_eq_of_prefixPair_map_eq fun n => ?_
  rw [map_prefixPair_jointPathLaw_eq h hX n,
    map_prefixPair_pathDisintegration h.measurable_directing n]

end Probability

end TauCeti
