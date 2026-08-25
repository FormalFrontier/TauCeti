/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.CutNorm
public import TauCeti.MeasureTheory.Measure.MapRestrictDensity

/-!
# The cut norm is invariant under measure-preserving pullback

If `f : Ω' → Ω` pushes a probability measure `ν` forward to `μ`, then a symmetric kernel `K` on
`(Ω, μ)` and its pullback `K.comap f` on `(Ω', ν)` have the *same* cut norm.

One inequality is elementary and already available: a measurable rectangle downstairs pulls back to
one upstairs with the same integral, so `cutNorm μ K ≤ cutNorm ν (K.comap f)`
(`cutNorm_le_cutNorm_comap`). The reverse inequality is the substance of this file, and it is not
elementary: a rectangle `S × T` upstairs need not be the preimage of anything, so its integral must
be *pushed down* rather than transported. The push is by conditional density: the part of `ν`
carried by `S` pushes forward to a measure below `μ`, whose Radon–Nikodym derivative
`mapRestrictDensity f ν μ S` is a `[0, 1]`-valued function on `Ω`, and the rectangle integral
upstairs
equals the pairing of `K` against the two densities (`rectIntegral_comap_eq_testIntegral`). Since
the cut norm already dominates every `[0, 1]`-test integral with no loss of constant
(`abs_testIntegral_le_cutNorm`), the bound follows.

**Why the `[0, 1]`-test form is the right input.** Replacing it by the signed cut norm would cost a
factor of `4` (`cutNormSigned_le_four_mul_cutNorm`) and give only a comparison, not an equality;
the sharp `abs_testIntegral_le_cutNorm` is what makes the invariance exact.

This is the analytic gate in front of the arbitrary-carrier triangle inequality for the cut
distance (Janson, Lemma 6.5). There a coupling of three carriers is built over the middle one, and
the two outer cut norms have to be compared with cut norms computed on the glued space along its
coordinate projections; those projections are measure preserving, and the comparison needed is
exactly the direction proved here. The triangle inequality itself is not proved in this file.

## Main results

* `TauCeti.DenseGraphLimits.SymmKernel.rectIntegral_comap_eq_testIntegral` — a rectangle integral
  of a pullback is a `[0, 1]`-test integral of the original kernel.
* `TauCeti.DenseGraphLimits.cutNorm_comap_le` — the cut norm does not increase under
  measure-preserving pullback.
* `TauCeti.DenseGraphLimits.cutNorm_comap` — hence it is invariant.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), §4 and Lemma 6.5.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §8.2.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 1 — the cut norm and its full basic
  API, as the prerequisite named there for the arbitrary-carrier triangle inequality.
-/

public section

noncomputable section

open MeasureTheory Set TauCeti.MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ : Measure Ω} {ν : Measure Ω'} {f : Ω' → Ω}

namespace SymmKernel

/-- **A rectangle integral upstairs is a `[0, 1]`-test integral downstairs.**  Integrating a
pullback over `S × T` weights each point of the base by the conditional density of `S`, resp. `T`,
above it.

This is the transport that replaces `rectIntegral_comap_preimage` when the rectangle upstairs is
*not* a preimage: instead of moving the rectangle, it moves the two indicators, which become the
`[0, 1]`-valued densities `mapRestrictDensity f ν μ S` and `mapRestrictDensity f ν μ T`. Neither set
needs to be
measurable. -/
theorem rectIntegral_comap_eq_testIntegral [IsFiniteMeasure ν]
    (hf : MeasurePreserving f ν μ) (K : SymmKernel Ω μ) (S T : Set Ω') :
    (K.comap f hf.measurable ν).rectIntegral ν S T =
      K.testIntegral μ (mapRestrictDensity f ν μ S) (mapRestrictDensity f ν μ T) := by
  let _ := isFiniteMeasure_of_measurePreserving hf
  have hu : Measurable (mapRestrictDensity f ν μ S) := measurable_mapRestrictDensity f ν μ S
  have hv : Measurable (mapRestrictDensity f ν μ T) := measurable_mapRestrictDensity f ν μ T
  have hu1 : ∀ x, mapRestrictDensity f ν μ S x ∈ Icc (-1 : ℝ) 1 := fun x =>
    ⟨by linarith [(mapRestrictDensity_mem_Icc f ν μ S x).1],
      (mapRestrictDensity_mem_Icc f ν μ S x).2⟩
  have hv1 : ∀ y, mapRestrictDensity f ν μ T y ∈ Icc (-1 : ℝ) 1 := fun y =>
    ⟨by linarith [(mapRestrictDensity_mem_Icc f ν μ T y).1],
      (mapRestrictDensity_mem_Icc f ν μ T y).2⟩
  have hinner : ∀ x : Ω',
      ∫ y in T, K (f x) (f y) ∂ν = K.partialIntegral μ (mapRestrictDensity f ν μ T) (f x) := by
    intro x
    rw [partialIntegral_def]
    exact (integral_mapRestrictDensity_mul hf T (g := fun b => K (f x) b)
      (K.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).symm
  calc (K.comap f hf.measurable ν).rectIntegral ν S T
      = ∫ x in S, ∫ y in T, K (f x) (f y) ∂ν ∂ν := by
        rw [rectIntegral_eq_setIntegral_setIntegral]
        simp only [comap_apply]
    _ = ∫ x in S, K.partialIntegral μ (mapRestrictDensity f ν μ T) (f x) ∂ν := by
        simp only [hinner]
    _ = ∫ a, mapRestrictDensity f ν μ S a *
          K.partialIntegral μ (mapRestrictDensity f ν μ T) a ∂μ :=
        (integral_mapRestrictDensity_mul hf S
          (K.measurable_partialIntegral μ hv).aestronglyMeasurable).symm
    _ = K.testIntegral μ (mapRestrictDensity f ν μ S) (mapRestrictDensity f ν μ T) :=
        (K.testIntegral_eq_integral_partialIntegral μ
          (K.integrable_testIntegrand μ hu hv hu1 hv1)).symm

end SymmKernel

/-- **The cut norm does not increase under measure-preserving pullback.**  This is the direction
that a change of variables cannot give, since a rectangle upstairs need not come from one
downstairs.

Every rectangle integral upstairs is a `[0, 1]`-test integral of `K` downstairs
(`rectIntegral_comap_eq_testIntegral`), and the cut norm dominates those with no loss of constant
(`abs_testIntegral_le_cutNorm`). -/
theorem cutNorm_comap_le [IsFiniteMeasure ν] [IsFiniteMeasure μ] (hf : MeasurePreserving f ν μ)
    (K : SymmKernel Ω μ) :
    cutNorm ν (K.comap f hf.measurable ν) ≤ cutNorm μ K :=
  cutNorm_le ν fun S _ T _ => by
    rw [SymmKernel.rectIntegral_comap_eq_testIntegral hf K S T]
    exact abs_testIntegral_le_cutNorm μ K (measurable_mapRestrictDensity f ν μ S)
      (measurable_mapRestrictDensity f ν μ T) (mapRestrictDensity_mem_Icc f ν μ S)
      (mapRestrictDensity_mem_Icc f ν μ T)

/-- **The cut norm is invariant under measure-preserving pullback.**  Pulling a kernel back along a
map from any carrier that maps measure preservingly *onto* the kernel's own carrier leaves its cut
norm unchanged.

The two inequalities have different characters: `cutNorm_le_cutNorm_comap` transports rectangles
along the map, while `cutNorm_comap_le` pushes them down by conditional density. -/
theorem cutNorm_comap [IsFiniteMeasure ν] [IsFiniteMeasure μ] (hf : MeasurePreserving f ν μ)
    (K : SymmKernel Ω μ) :
    cutNorm ν (K.comap f hf.measurable ν) = cutNorm μ K :=
  le_antisymm (cutNorm_comap_le hf K) (cutNorm_le_cutNorm_comap μ hf K)

end DenseGraphLimits

end TauCeti
