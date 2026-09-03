/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Smooth
public import TauCeti.Analysis.Fredholm.UniversalLevelSet
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Fredholm.SardSmale

/-!
# Parameter maps on universal Fredholm level sets

Let `f : E × Λ → F` be a parametrized equation and suppose that its total linearization at a
solution `(x, l)` is `D₁.coprod D₂`. When this linearization is surjective with complemented
kernel, `TauCeti.levelSetChart` parametrizes the universal level set near `(x, l)` by
`ker (D₁.coprod D₂)`. Composing its inverse with the projection to `Λ` gives the local parameter
map `TauCeti.levelSetParameterMap`.

This file calculates that map's derivative at the chart origin. It is exactly
`TauCeti.parameterProj D₁ D₂`, the linear parameter projection developed in
`TauCeti.Analysis.Fredholm.Parametric`. Every statement about that linear map therefore transfers
to the derivative at the origin: it is surjective exactly when `D₁` is, by
`TauCeti.surjective_fderiv_levelSetParameterMap_iff`; it has the same index as `D₁`, by
`TauCeti.index_fderiv_levelSetParameterMap`; and over a complete `RCLike` field it is Fredholm as
soon as `D₁` is, by `TauCeti.isFredholm_fderiv_levelSetParameterMap`. The final theorem applies
local
Sard--Smale to show that, inside the chart target, nearby critical values of the parameter map
form a closed nowhere dense set. The identification of criticality with failure of regularity for
the fixed-parameter equation is proved only at the chart origin; the nearby critical-value
conclusion is not yet a statement about regular parameters of that equation.

These results are the local nonlinear calculation in the parametric transversality package of
McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.3. Passing
from this one chart to a residual set of parameters for a whole universal moduli space requires
smooth compatibility and a countable cover, and is not asserted here.

## Main results

* `TauCeti.hasStrictFDerivAt_levelSetParameterMap`: the derivative at the chart origin is the
  linear parameter projection.
* `TauCeti.levelSetParameterMap_levelSetChart`: on the chart source, the local parameter map is
  the parameter projection of the universal level set.
* `TauCeti.exists_apply_levelSetParameterMap_eq`: every value of the local parameter map is a
  parameter at which the equation has a solution.
* `TauCeti.surjective_fderiv_levelSetParameterMap_iff`: the chart origin is a regular point of the
  local parameter map exactly when the fixed-parameter linearization is surjective.
* `TauCeti.index_fderiv_levelSetParameterMap`: that derivative has the index of the
  fixed-parameter linearization.
* `TauCeti.isFredholm_fderiv_levelSetParameterMap`: over a complete `RCLike` field, that
  derivative is Fredholm as soon as the fixed-parameter linearization is.
* `TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints_levelSetParameterMap`:
  local Sard--Smale for the parameter map of a universal level set.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965),
  861--866.
-/

public section

open Function Module Set
open scoped ContDiff Topology

namespace TauCeti

variable {K E Λ F : Type*} [NontriviallyNormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
variable [NormedAddCommGroup Λ] [NormedSpace K Λ] [CompleteSpace Λ]
variable [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]
variable {f : E × Λ → F} {D₁ : E →L[K] F} {D₂ : Λ →L[K] F}
variable {x : E} {l : Λ} {c : F}

/-- The local projection from a universal level set to its parameter space, written in the
regular-level-set chart at `(x, l)`.

The function is meaningful on the target of the level-set chart, a neighbourhood of the origin.
As with `TauCeti.levelSetChart`, its value outside that target is an irrelevant total extension. -/
noncomputable def levelSetParameterMap
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) : (D₁.coprod D₂).ker → Λ :=
  fun k ↦ (((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k :
    ↥{z | f z = c}) : E × Λ).2

/-- The local parameter map reads the parameter component of the inverse level-set chart. -/
@[simp]
theorem levelSetParameterMap_apply
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) (k : (D₁.coprod D₂).ker) :
    levelSetParameterMap hf hD hker hxl k =
      (((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k :
        ↥{z | f z = c}) : E × Λ).2 := by
  unfold levelSetParameterMap
  rfl

/-- At the chart origin, the local parameter map returns the base parameter. -/
theorem levelSetParameterMap_zero
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    levelSetParameterMap hf hD hker hxl 0 = l := by
  rw [levelSetParameterMap_apply, levelSetChart_symm_zero]

/-- On the source of the level-set chart, the local parameter map really is the parameter
projection of the universal level set: it sends the chart image of a solution `z` back to the
parameter component of `z`. -/
theorem levelSetParameterMap_levelSetChart
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) {z : ↥{z | f z = c}}
    (hz : z ∈ (levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).source) :
    levelSetParameterMap hf hD hker hxl
        (levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl z) = ((z : E × Λ)).2 := by
  rw [levelSetParameterMap_apply,
    (levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).left_inv hz]

/-- Every value of the local parameter map is a parameter for which the equation has a solution:
the chart parametrizes the universal level set, so the point it produces solves the equation at
the parameter that the map returns. -/
theorem exists_apply_levelSetParameterMap_eq
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) (k : (D₁.coprod D₂).ker) :
    ∃ x' : E, f (x', levelSetParameterMap hf hD hker hxl k) = c := by
  refine ⟨(((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k :
    ↥{z | f z = c}) : E × Λ).1, ?_⟩
  rw [levelSetParameterMap_apply]
  exact ((levelSetChart hf (LinearMap.range_eq_top.mpr hD) hker hxl).symm k).2

/-- The local parameter map is as smooth at the chart origin as the parametrized equation. -/
theorem contDiffAt_levelSetParameterMap {n : ℕ∞ω}
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hcont : ContDiffAt K n f (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    ContDiffAt K n (levelSetParameterMap hf hD hker hxl) 0 := by
  have hchart := contDiffAt_coe_levelSetChart_symm hf hcont
    (LinearMap.range_eq_top.mpr hD) hker hxl
  rw [funext fun k ↦ levelSetParameterMap_apply hf hD hker hxl k]
  exact hchart.snd

/-- The derivative at the chart origin of the local parameter map is the restriction of the
ambient parameter projection to the kernel of the total linearization. -/
theorem hasStrictFDerivAt_levelSetParameterMap
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    HasStrictFDerivAt (levelSetParameterMap hf hD hker hxl)
      (parameterProj D₁ D₂) 0 := by
  have hchart := hasStrictFDerivAt_coe_levelSetChart_symm hf
    (LinearMap.range_eq_top.mpr hD) hker hxl
  have hcomp := hchart.snd
  have hproj : parameterProj D₁ D₂ =
      (ContinuousLinearMap.snd K E Λ).comp (D₁.coprod D₂).ker.subtypeL := by
    ext v
    simp
  rw [hproj, funext fun k ↦ levelSetParameterMap_apply hf hD hker hxl k]
  exact hcomp

/-- The Fréchet derivative of the local parameter map at the chart origin is the linear
parameter projection. -/
@[simp]
theorem fderiv_levelSetParameterMap
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    fderiv K (levelSetParameterMap hf hD hker hxl) 0 = parameterProj D₁ D₂ :=
  (hasStrictFDerivAt_levelSetParameterMap hf hD hker hxl).hasFDerivAt.fderiv

/-- **Regularity at the chart origin.** The derivative of the local parameter map at the chart
origin is surjective exactly when the fixed-parameter linearization is. This is the
transversality criterion the parametric package is aimed at, transported to the nonlinear map by
`TauCeti.fderiv_levelSetParameterMap`. -/
theorem surjective_fderiv_levelSetParameterMap_iff
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    Surjective (fderiv K (levelSetParameterMap hf hD hker hxl) 0) ↔ Surjective D₁ := by
  rw [fderiv_levelSetParameterMap]
  exact parameterProj_surjective_iff D₁ D₂ hD

/-- The derivative of the local parameter map at the chart origin has the same index as the
fixed-parameter linearization. Neither map is assumed Fredholm: both indices are differences of
`Module.finrank`s, junk values included. -/
theorem index_fderiv_levelSetParameterMap
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hker : (D₁.coprod D₂).ker.ClosedComplemented)
    (hxl : f (x, l) = c) :
    ContinuousLinearMap.index (fderiv K (levelSetParameterMap hf hD hker hxl) 0) =
      ContinuousLinearMap.index D₁ := by
  rw [fderiv_levelSetParameterMap]
  exact index_parameterProj D₁ D₂ hD

section RCLike

variable [IsRCLikeNormedField K] [CompleteSpace K]

/-- If the fixed-parameter linearization is Fredholm, then so is the derivative at the origin of
the local parameter map. -/
theorem isFredholm_fderiv_levelSetParameterMap
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hD : Surjective (D₁.coprod D₂))
    (hxl : f (x, l) = c) (hD₁ : ContinuousLinearMap.IsFredholm D₁) :
    ContinuousLinearMap.IsFredholm
      (fderiv K (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl) 0) := by
  rw [fderiv_levelSetParameterMap]
  exact isFredholm_parameterProj D₁ D₂ hD₁

end RCLike

section Real

variable {E Λ F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace Λ]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {f : E × Λ → F} {D₁ : E →L[ℝ] F} {D₂ : Λ →L[ℝ] F}
variable {x : E} {l : Λ} {c : F}

/-- **Local parametric Sard--Smale.** In a regular chart of a universal level set whose
fixed-parameter linearization is Fredholm, the critical values of the local parameter map coming
from a sufficiently small neighbourhood of the chart origin form a closed nowhere dense set.

The neighbourhood is contained in the target of the level-set chart, on which the local parameter
map really is the parameter projection of the universal level set rather than the irrelevant total
extension of `TauCeti.levelSetParameterMap`. It can also be confined to any prescribed
neighbourhood `U` of the chart origin, as
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints` allows; take `U = univ` for
the plain statement.

Here criticality is defined intrinsically for the local parameter map. Its equivalence with
failure of surjectivity of the fixed-parameter linearization has only been established at the
chart origin, by `TauCeti.surjective_fderiv_levelSetParameterMap_iff`, so this result does not yet
identify nearby critical values with non-regular parameters of the original equation.

The differentiability threshold is the one currently supplied by
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints`, rewritten using the fact
that the kernel of `parameterProj D₁ D₂` has the same dimension as `ker D₁`. -/
theorem exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints_levelSetParameterMap
    {n : ℕ∞ω} {U : Set (D₁.coprod D₂).ker}
    (hf : HasStrictFDerivAt f (D₁.coprod D₂) (x, l))
    (hcont : ContDiffAt ℝ n f (x, l))
    (hD₁ : ContinuousLinearMap.IsFredholm D₁)
    (hD : Surjective (D₁.coprod D₂))
    (hxl : f (x, l) = c)
    (hn : ((finrank ℝ D₁.ker * finrank ℝ D₁.ker + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hU : U ∈ 𝓝 (0 : (D₁.coprod D₂).ker)) :
    ∃ N ∈ 𝓝 (0 : (D₁.coprod D₂).ker),
      N ⊆ U ∩ (levelSetChart hf (LinearMap.range_eq_top.mpr hD)
        (hD₁.closedComplemented_ker_coprod hD) hxl).target ∧
      IsClosed (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl ''
        (N ∩ {k | ¬ Surjective (fderiv ℝ
          (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl) k)})) ∧
      IsNowhereDense (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl ''
        (N ∩ {k | ¬ Surjective (fderiv ℝ
          (levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl) k)})) := by
  let g := levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl
  have hg : ContDiffAt ℝ n g 0 :=
    contDiffAt_levelSetParameterMap hf hcont hD (hD₁.closedComplemented_ker_coprod hD) hxl
  have hg' : fderiv ℝ g 0 = parameterProj D₁ D₂ :=
    fderiv_levelSetParameterMap hf hD (hD₁.closedComplemented_ker_coprod hD) hxl
  have hn' :
      ((finrank ℝ (parameterProj D₁ D₂).ker * finrank ℝ (parameterProj D₁ D₂).ker + 1 : ℕ) :
        ℕ∞ω) ≤ n := by
    simpa only [finrank_ker_parameterProj] using hn
  have hFred := isFredholm_fderiv_levelSetParameterMap hf hD hxl hD₁
  have hn'' :
      ((finrank ℝ (fderiv ℝ g 0).ker * finrank ℝ (fderiv ℝ g 0).ker + 1 : ℕ) : ℕ∞ω) ≤ n := by
    rw [hg']
    exact hn'
  have htarget := (levelSetChart hf (LinearMap.range_eq_top.mpr hD)
    (hD₁.closedComplemented_ker_coprod hD) hxl).open_target.mem_nhds
      (mem_levelSetChart_target hf (LinearMap.range_eq_top.mpr hD)
        (hD₁.closedComplemented_ker_coprod hD) hxl)
  exact exists_mem_nhds_isClosed_isNowhereDense_image_criticalPoints hg hFred hn''
    (Filter.inter_mem hU htarget)

end Real

end TauCeti

end
