/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# The along-curve derivative of a pulled-back vector field

`CovariantDerivative.alongCurveWithin` differentiates a tangent field along a curve by the
moving-chart formula `v' + Γ(v, u')` of
`TauCeti/Geometry/Manifold/VectorBundle/CovariantDerivative/AlongCurve/Basic.lean`, which reads
the curve and the field in the chart centred at the current point.  This file identifies that
formula for a field which is *pulled back* from an ambient vector field, `V t = X (γ t)`: there
the formula returns `∇_{γ'(t)} X`, the ambient covariant derivative of `X` in the direction of the
velocity of `γ`.  This is the property that pins the along-curve derivative down and makes it
chart independent on pulled-back fields, and it is what lets a connection-based geodesic equation
be stated through the along-curve API.

The identification is proved in an arbitrary chart, not only in the moving one: for any `x` whose
chart contains `γ t`, the coordinate formula computed in the chart at `x` is the reading of
`∇_{γ'(t)} X` in the tangent-bundle trivialization at `x`.  Transporting back therefore gives the
same tangent vector for every such `x`.

The velocity of the curve is carried by a `HasMFDerivWithinAt` hypothesis, in the
`ContinuousLinearMap.smulRight 1 w` form used by Mathlib's integral-curve API, so that no junk
value can leak in; `CovariantDerivative.alongCurveWithin_pullback_mfderivWithin` restates the
result for the canonical velocity `mfderivWithin 𝓘(𝕜, 𝕜) I γ s t 1`.

## Main results

* `TauCeti.Manifold.derivWithin_extChartAt_comp`: the derivative of a curve read in the chart at
  `x` is the reading of its velocity in the tangent-bundle trivialization at `x`.
* `TauCeti.Manifold.derivWithin_sectionCoord_pullback`: the derivative of the coordinate reading
  of a pulled-back field is the reading of the flat frame derivative in the direction of the
  velocity.
* `CovariantDerivative.alongCurveInChartWithin_pullback`: the coordinate formula in the chart at
  `x`, for a pulled-back field, is the reading of `∇_{γ'(t)} X`.
* `CovariantDerivative.alongCurveWithin_pullback` and
  `CovariantDerivative.alongCurve_pullback`: the along-curve derivative of a pulled-back field is
  `∇_{γ'(t)} X`, within a parameter set and unrestricted.
* `CovariantDerivative.symmL_alongCurveInChartWithin_pullback`: on pulled-back fields the
  coordinate formula is chart independent -- reading it in any chart around `γ t` and transporting
  back gives the moving-chart value.
* `CovariantDerivative.alongCurveWithin_pullback_mfderivWithin`: the same identification with the
  velocity written as `mfderivWithin 𝓘(𝕜, 𝕜) I γ s t 1`.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Covariant derivative along a curve": agreement with the ambient derivative for a
  pulled-back vector field.
* M. P. do Carmo, *Riemannian Geometry*, Birkhauser, 1992, Ch. 2, Proposition 2.2(c).
-/

public section

open Bundle Filter Module Set
open scoped Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

variable (γ : 𝕜 → M) (X : Π y : M, TangentSpace I y)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The derivative of a curve read in the chart centred at `x`, taken within a parameter set with
a unique derivative there, is the reading of the velocity of the curve in the tangent-bundle
trivialization at `x`.  The chart need not be the one centred at the current point of the
curve. -/
theorem derivWithin_extChartAt_comp {x : M} {s : Set 𝕜} {t : 𝕜} {w : TangentSpace I (γ t)}
    (hx : γ t ∈ (chartAt H x).source) (hu : UniqueDiffWithinAt 𝕜 s t)
    (hγ : HasMFDerivAt[s] γ t (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) w)) :
    derivWithin (extChartAt I x ∘ γ) s t =
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 (γ t) w := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hx]
  set D := mfderiv% (extChartAt I x) (γ t)
  have hchart : HasMFDerivAt% (extChartAt I x) (γ t) D :=
    (mdifferentiableAt_extChartAt hx).hasMFDerivAt
  -- The chain rule for the chart composed with the curve; the continuous linear maps
  -- `D ∘L (1.smulRight w)` and `1.smulRight (D w)` agree by linearity of `D`.
  have hcomp : HasMFDerivAt[s] (extChartAt I x ∘ γ) t
      (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (D w)) :=
    (hchart.comp_hasMFDerivWithinAt (hf := hγ)).congr_mfderiv (by
      ext
      exact D.map_smul (1 : 𝕜) w)
  have hderiv : HasDerivWithinAt (extChartAt I x ∘ γ) (D w) s t := hcomp.hasFDerivWithinAt
  exact hderiv.derivWithin hu

/-- Along a curve, the derivative of the coordinate reading of a pulled-back vector field is the
reading of the flat frame derivative of that field in the direction of the velocity.  Both
readings are taken in the tangent-bundle trivialization at `x`, whose base set contains the
current point of the curve. -/
theorem derivWithin_sectionCoord_pullback {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 E) {x : M}
    {s : Set 𝕜} {t : 𝕜} {w : TangentSpace I (γ t)}
    (hy : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet) (hu : UniqueDiffWithinAt 𝕜 s t)
    (hγ : HasMFDerivAt[s] γ t (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) w))
    (hX : MDiffAt (T% X) (γ t)) :
    derivWithin (sectionCoord (F := E) γ (fun r ↦ X (γ r)) x) s t =
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 (γ t)
        (frameCovariantDerivative I b (trivializationAt E (TangentSpace I) x) X (γ t) w) := by
  set e := trivializationAt E (TangentSpace I) x
  set σ : ι → M → 𝕜 := fun i ↦ (LinearMap.piApply (e.localFrameCoeff I b i)) X
  -- The coordinate reading of a section is the sum of its frame coefficients.
  have hread : ∀ y ∈ e.baseSet, e.continuousLinearMapAt 𝕜 y (X y) = ∑ i, σ i y • b i := by
    intro y hyb
    have h : ∀ i, σ i y = b.repr (e.continuousLinearMapAt 𝕜 y (X y)) i := fun i ↦ by
      have hcoe : σ i y = e.localFrameCoeff I b i y (X y) := (rfl)
      rw [hcoe, e.localFrameCoeff_eq_coeff (s := X) hyb,
        Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) e hyb]
    simp only [h]
    exact (b.sum_repr _).symm
  -- Each frame coefficient is differentiable along the curve, with the expected derivative.
  have hcoeff : ∀ i, HasDerivWithinAt (fun r ↦ σ i (γ r)) (d% (σ i) (γ t) w) s t := by
    intro i
    have hσ : MDiffAt (σ i) (γ t) := mdifferentiableAt_localFrameCoeff b hy hX i
    have hcomp : HasMFDerivAt[s] (fun r ↦ σ i (γ r)) t
        (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (d% (σ i) (γ t) w)) :=
      (hσ.hasMFDerivAt.comp_hasMFDerivWithinAt (hf := hγ)).congr_mfderiv (by
        ext
        exact (d% (σ i) (γ t)).map_smul (1 : 𝕜) w)
    exact hcomp.hasFDerivWithinAt
  have hfun : (∑ i : ι, fun r ↦ σ i (γ r) • b i) = fun r ↦ ∑ i, σ i (γ r) • b i := by
    funext r
    simp [Finset.sum_apply]
  have hsum : HasDerivWithinAt (fun r ↦ ∑ i, σ i (γ r) • b i)
      (∑ i, d% (σ i) (γ t) w • b i) s t :=
    hfun ▸ HasDerivWithinAt.sum fun i (_ : i ∈ Finset.univ) ↦ (hcoeff i).smul_const (b i)
  have hbase : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    hγ.1.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hy)
  have hEq : sectionCoord (F := E) γ (fun r ↦ X (γ r)) x =ᶠ[𝓝[s] t]
      fun r ↦ ∑ i, σ i (γ r) • b i :=
    hbase.mono fun r hr ↦ by rw [sectionCoord_apply, hread _ hr]
  have hpoint : sectionCoord (F := E) γ (fun r ↦ X (γ r)) x t =
      (fun r ↦ ∑ i, σ i (γ r) • b i) t := by
    rw [sectionCoord_apply, hread _ hy]
  rw [(hsum.congr_of_eventuallyEq hEq hpoint).derivWithin hu, frameCovariantDerivative_apply,
    map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul]
  have hframe : e.continuousLinearMapAt 𝕜 (γ t) (e.localFrame b i (γ t)) = b i := by
    simp [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem, hy,
      Bundle.Trivialization.localFrame_apply_of_mem_baseSet, Bundle.Trivialization.basisAt]
  rw [hframe]

end TauCeti.Manifold

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

variable (cov : _root_.CovariantDerivative I E (fun y : M ↦ TangentSpace I y))
  (γ : 𝕜 → M) (X : Π y : M, TangentSpace I y)

/-- The moving-chart coordinate formula, evaluated in the chart at an arbitrary point `x` whose
base set contains `γ t`, computes the reading of the ambient covariant derivative `∇_{γ'(t)} X`
in the tangent-bundle trivialization at `x`, whenever the differentiated field is pulled back
from the vector field `X`. -/
theorem alongCurveInChartWithin_pullback {x : M} {s : Set 𝕜} {t : 𝕜} {w : TangentSpace I (γ t)}
    (hy : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet) (hu : UniqueDiffWithinAt 𝕜 s t)
    (hγ : HasMFDerivAt[s] γ t (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) w))
    (hX : MDiffAt (T% X) (γ t)) :
    alongCurveInChartWithin cov γ (fun r ↦ X (γ r)) s x t =
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 (γ t) (cov X (γ t) w) := by
  set e := trivializationAt E (TangentSpace I) x
  set b := Module.finBasis 𝕜 E
  set hcov := cov.isCovariantDerivativeOn (s := e.baseSet)
  -- The two summands of the coordinate formula are the readings of the flat frame derivative and
  -- of the Christoffel form, whose sum is the covariant derivative.
  rw [alongCurveInChartWithin_apply, derivWithin_sectionCoord_pullback γ X b hy hu hγ hX,
    derivWithin_extChartAt_comp γ hy hu hγ, christoffelMap_apply b hcov hy, sectionCoord_apply,
    e.symmL_continuousLinearMapAt (R := 𝕜) hy, e.symmL_continuousLinearMapAt (R := 𝕜) hy,
    ← map_add, covariantDerivative_eq_add_christoffelForm b hcov hy hX]
  rfl

/-- **Agreement with the ambient covariant derivative.** The derivative along `γ` of the field
pulled back from a vector field `X` is `∇_{γ'(t)} X`, the ambient covariant derivative of `X` in
the direction of the velocity of `γ`. -/
theorem alongCurveWithin_pullback {s : Set 𝕜} {t : 𝕜} {w : TangentSpace I (γ t)}
    (hu : UniqueDiffWithinAt 𝕜 s t)
    (hγ : HasMFDerivAt[s] γ t (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) w))
    (hX : MDiffAt (T% X) (γ t)) :
    alongCurveWithin cov γ (fun r ↦ X (γ r)) s t = cov X (γ t) w := by
  have hmem := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  rw [alongCurveWithin_apply, alongCurveInChartWithin_pullback cov γ X hmem hu hγ hX,
    (trivializationAt E (TangentSpace I) (γ t)).symmL_continuousLinearMapAt (R := 𝕜) hmem]

/-- **Chart independence on pulled-back fields.** Reading the coordinate formula in the chart at
any point `x` whose base set contains `γ t`, and transporting the result back to
`TangentSpace I (γ t)`, gives the moving-chart value. -/
theorem symmL_alongCurveInChartWithin_pullback {x : M} {s : Set 𝕜} {t : 𝕜}
    {w : TangentSpace I (γ t)}
    (hy : γ t ∈ (trivializationAt E (TangentSpace I) x).baseSet) (hu : UniqueDiffWithinAt 𝕜 s t)
    (hγ : HasMFDerivAt[s] γ t (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) w))
    (hX : MDiffAt (T% X) (γ t)) :
    (trivializationAt E (TangentSpace I) x).symmL 𝕜 (γ t)
        (alongCurveInChartWithin cov γ (fun r ↦ X (γ r)) s x t) =
      alongCurveWithin cov γ (fun r ↦ X (γ r)) s t := by
  rw [alongCurveInChartWithin_pullback cov γ X hy hu hγ hX,
    (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt (R := 𝕜) hy,
    alongCurveWithin_pullback cov γ X hu hγ hX]

/-- The unrestricted along-curve derivative of a pulled-back vector field is the ambient covariant
derivative in the direction of the velocity of the curve. -/
theorem alongCurve_pullback {t : 𝕜} {w : TangentSpace I (γ t)}
    (hγ : HasMFDerivAt% γ t (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) w))
    (hX : MDiffAt (T% X) (γ t)) :
    alongCurve cov γ (fun r ↦ X (γ r)) t = cov X (γ t) w := by
  rw [← alongCurveWithin_univ]
  exact alongCurveWithin_pullback cov γ X uniqueDiffWithinAt_univ hγ.hasMFDerivWithinAt hX

/-- Agreement with the ambient covariant derivative, with the velocity of the curve written as the
canonical `mfderivWithin 𝓘(𝕜, 𝕜) I γ s t 1`. -/
theorem alongCurveWithin_pullback_mfderivWithin {s : Set 𝕜} {t : 𝕜}
    (hu : UniqueDiffWithinAt 𝕜 s t) (hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t)
    (hX : MDiffAt (T% X) (γ t)) :
    alongCurveWithin cov γ (fun r ↦ X (γ r)) s t =
      cov X (γ t) (mfderivWithin 𝓘(𝕜, 𝕜) I γ s t (1 : 𝕜)) := by
  refine alongCurveWithin_pullback cov γ X hu (hγ.hasMFDerivWithinAt.congr_mfderiv ?_) hX
  ext
  -- The tangent space of the scalar model is definitionally `𝕜`, but its topology instance blocks
  -- rewriting by `ContinuousLinearMap.smulRight_apply` until that identification is exposed.
  change (mfderivWithin 𝓘(𝕜, 𝕜) I γ s t) (1 : 𝕜) =
    (1 : 𝕜) • (mfderivWithin 𝓘(𝕜, 𝕜) I γ s t) (1 : 𝕜)
  rw [one_smul]

end CovariantDerivative
