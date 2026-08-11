/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Ergodic.FixedSpace
public import Mathlib.Dynamics.BirkhoffSum.NormedSpace
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-!
# Mean ergodic projection for measure-preserving maps

This file defines the orthogonal projection from vector-valued `L²` onto the fixed space of the
composition operator associated to a measure-preserving endomorphism. It characterizes the
projection by membership, fixed points, its range, and the orthogonal error.

The main theorem, `birkhoffAverage_tendsto_metProjection`, says that the Birkhoff averages of the
composition operator converge in `L²` to this projection. It specializes Mathlib's von Neumann
mean ergodic theorem
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` to the `L²` composition
isometry.
-/

public section

noncomputable section

open Function MeasureTheory Filter
open scoped ENNReal Topology

namespace TauCeti

namespace Probability

variable {Ω 𝕜 E : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {μ : Measure Ω}

/-- The mean-ergodic projection onto the `L²` observables fixed by composition with `T`. -/
def metProjection (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Lp E 2 μ →L[𝕜] Lp E 2 μ :=
  (fixedSpace (𝕜 := 𝕜) (E := E) (p := 2) T hT).starProjection

/-- The mean-ergodic projection takes values in the fixed space. -/
theorem metProjection_mem_fixedSpace (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Lp E 2 μ) :
    metProjection (𝕜 := 𝕜) T hT g ∈ fixedSpace (𝕜 := 𝕜) (E := E) (p := 2) T hT := by
  rw [metProjection]
  exact Submodule.starProjection_apply_mem _ _

/-- The mean-ergodic projection fixes exactly the invariant `L²` observables. -/
@[simp]
theorem metProjection_eq_self_iff (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Lp E 2 μ) :
    metProjection (𝕜 := 𝕜) T hT g = g ↔
      g ∈ fixedSpace (𝕜 := 𝕜) (E := E) (p := 2) T hT := by
  rw [metProjection]
  exact Submodule.starProjection_eq_self_iff

/-- The range of the mean-ergodic projection is the fixed space. -/
@[simp]
theorem range_metProjection (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    (metProjection (𝕜 := 𝕜) (E := E) T hT).range =
      fixedSpace (𝕜 := 𝕜) (E := E) (p := 2) T hT := by
  rw [metProjection]
  exact Submodule.range_starProjection _

/-- The error after mean-ergodic projection is orthogonal to the fixed space. -/
@[simp]
theorem sub_metProjection_mem_orthogonal (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Lp E 2 μ) :
    g - metProjection (𝕜 := 𝕜) T hT g ∈
      (fixedSpace (𝕜 := 𝕜) (E := E) (p := 2) T hT)ᗮ := by
  rw [metProjection]
  exact Submodule.sub_starProjection_mem_orthogonal _

/-- The mean-ergodic projection for the identity transformation is the identity operator. -/
@[simp]
theorem metProjection_id :
    metProjection (μ := μ) (𝕜 := 𝕜) (E := E) id (MeasurePreserving.id μ) =
      ContinuousLinearMap.id 𝕜 (Lp E 2 μ) := by
  apply ContinuousLinearMap.ext
  intro g
  rw [metProjection]
  exact Submodule.starProjection_eq_self_iff.mpr
    ((mem_fixedSpace_iff (𝕜 := 𝕜) (E := E) (p := 2) (MeasurePreserving.id μ) g).2
      (Lp.compMeasurePreserving_id_apply g))

/-- The Birkhoff averages of the `L²` composition operator converge to the mean-ergodic
projection onto its fixed space. -/
theorem birkhoffAverage_tendsto_metProjection (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (g : Lp E 2 μ) :
    Tendsto
      (birkhoffAverage 𝕜
        (Lp.compMeasurePreservingₗᵢ 𝕜 T hT).toContinuousLinearMap id · g)
      atTop (𝓝 (metProjection (𝕜 := 𝕜) T hT g)) := by
  let Uᵢ : Lp E 2 μ →ₗᵢ[𝕜] Lp E 2 μ := Lp.compMeasurePreservingₗᵢ 𝕜 T hT
  let U : Lp E 2 μ →L[𝕜] Lp E 2 μ := Uᵢ.toContinuousLinearMap
  have hU_norm : ‖U‖ ≤ 1 := Uᵢ.norm_toContinuousLinearMap_le
  have hU := U.tendsto_birkhoffAverage_orthogonalProjection hU_norm g
  have hspace :
      U.eqLocus (1 : Lp E 2 μ →L[𝕜] Lp E 2 μ) =
        fixedSpace (𝕜 := 𝕜) (E := E) (p := 2) T hT := by
    simpa only [U, Uᵢ] using
      (fixedSpace_eq_eqLocus (𝕜 := 𝕜) (E := E) (p := 2) T hT).symm
  simpa only [U, Uᵢ, metProjection, hspace,
    Submodule.coe_orthogonalProjectionOnto_apply] using hU

end Probability

end TauCeti
