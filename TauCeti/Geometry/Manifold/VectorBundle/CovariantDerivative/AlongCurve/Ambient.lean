/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# The along-curve derivative of a vector field restricted to the curve

`AlongCurve/Basic.lean` builds the moving-chart candidate `CovariantDerivative.alongCurveWithin`
for the covariant derivative of a tangent field along a curve, and proves its algebra and
locality laws.  Those laws alone do not pin the operator down: they hold for the coordinate
expression in any chart.  What identifies it is its behaviour on the fields that come from the
ambient manifold.  This file proves that identification: if `X` is a tangent vector field which is
differentiable at `γ t`, and `γ` has manifold derivative the velocity `w` at `t` within a
parameter set `s`, then

`D (X ∘ γ) / dt = ∇_w X`.

This is do Carmo's characterizing property (c) of covariant differentiation along a curve, and it
is what makes the moving-chart formula the covariant derivative rather than a chart-dependent
candidate.  Reading the curve in the chart *centred at the current point* `γ t` is what makes the
proof short: over its own base point the canonical tangent-bundle trivialization is the identity,
so the coordinate reading of the field is the field, the chart derivative of the curve is the
velocity, and the model-space Christoffel map is the Christoffel form.

The chain rule for a function on the manifold restricted to the curve, and the reading of the
curve in the chart centred at the current point, are supplied by
`TauCeti/Geometry/Manifold/MFDeriv/Curve.lean`.

## Main definitions and results

* `CovariantDerivative.alongCurveWithin_comp_vectorField`: the along-curve derivative of a vector
  field restricted to the curve is the ambient covariant derivative in the direction of the
  velocity, with `CovariantDerivative.alongCurve_comp_vectorField` its unrestricted case.
* `CovariantDerivative.differentiableWithinAt_sectionCoord_comp_vectorField`: the coordinate
  reading of such a field is differentiable, which is the side condition the algebra laws of
  `AlongCurve/Basic.lean` ask for.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Covariant derivative along a curve", the clause "agreement with the ambient derivative
  for a pulled-back vector field".
* M. P. do Carmo, *Riemannian Geometry*, Birkhauser, 1992, Ch. 2, Proposition 2.2 (c).
-/

public section

open Bundle FiberBundle Module
open scoped Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

variable (cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  {γ : 𝕜 → M} {X : Π y : M, TangentSpace I y} {s : Set 𝕜} {t : 𝕜} {w : TangentSpace I (γ t)}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
/-- Over `e.baseSet` the coordinate reading of a section in `e` is the coefficient vector of the
section in the local frame attached to `e`. -/
private theorem continuousLinearMapAt_eq_sum_localFrameCoeff
    {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 E)
    {e : Trivialization E (TotalSpace.proj : TangentBundle I M → M)} [MemTrivializationAtlas e]
    {y : M} (hy : y ∈ e.baseSet) :
    e.continuousLinearMapAt 𝕜 y (X y) = ∑ i, e.localFrameCoeff I b i y (X y) • b i := by
  rw [← b.sum_repr (e.continuousLinearMapAt 𝕜 y (X y))]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg (fun c ↦ c • b i) ?_
  rw [e.localFrameCoeff_apply_of_mem_baseSet b hy X i]
  simp [Bundle.Trivialization.basisAt,
    Bundle.Trivialization.continuousLinearMapAt_apply_of_mem, hy]

/-- The coordinate reading of a vector field restricted to a curve differentiates to the flat
frame derivative of the field in the direction of the velocity. -/
private theorem hasDerivWithinAt_sectionCoord_comp_vectorField
    (hX : MDifferentiableAt I (I.prod 𝓘(𝕜, E)) (fun y ↦ TotalSpace.mk' E y (X y)) (γ t))
    (hγ : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w)) :
    HasDerivWithinAt (sectionCoord (F := E) γ (fun r ↦ X (γ r)) (γ t))
      (∑ i, mvfderiv I ((LinearMap.piApply
        ((trivializationAt E (TangentSpace I) (γ t)).localFrameCoeff I
          (Module.finBasis 𝕜 E) i)) X) (γ t) w • Module.finBasis 𝕜 E i) s t := by
  have hx : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have heq : (fun r ↦ sectionCoord (F := E) γ (fun r ↦ X (γ r)) (γ t) r)
      =ᶠ[𝓝[s] t] fun r ↦ ∑ i, (trivializationAt E (TangentSpace I) (γ t)).localFrameCoeff I
          (Module.finBasis 𝕜 E) i (γ r) (X (γ r)) • Module.finBasis 𝕜 E i := by
    filter_upwards [hγ.1.preimage_mem_nhdsWithin
      ((trivializationAt E (TangentSpace I) (γ t)).open_baseSet.mem_nhds hx)] with r hr
    rw [sectionCoord_apply]
    exact continuousLinearMapAt_eq_sum_localFrameCoeff (Module.finBasis 𝕜 E) hr
  have hsum : HasDerivWithinAt
      (fun r ↦ ∑ i, (trivializationAt E (TangentSpace I) (γ t)).localFrameCoeff I
        (Module.finBasis 𝕜 E) i (γ r) (X (γ r)) • Module.finBasis 𝕜 E i)
      (∑ i, mvfderiv I ((LinearMap.piApply
        ((trivializationAt E (TangentSpace I) (γ t)).localFrameCoeff I
          (Module.finBasis 𝕜 E) i)) X) (γ t) w • Module.finBasis 𝕜 E i) s t := by
    refine HasDerivWithinAt.fun_sum
      (A := fun i r ↦ (trivializationAt E (TangentSpace I) (γ t)).localFrameCoeff I
        (Module.finBasis 𝕜 E) i (γ r) (X (γ r)) • Module.finBasis 𝕜 E i)
      (A' := fun i ↦ mvfderiv I ((LinearMap.piApply
        ((trivializationAt E (TangentSpace I) (γ t)).localFrameCoeff I
          (Module.finBasis 𝕜 E) i)) X) (γ t) w • Module.finBasis 𝕜 E i) fun i _ ↦ ?_
    exact (hasDerivWithinAt_comp_curve
      (mdifferentiableAt_localFrameCoeff (Module.finBasis 𝕜 E) hx hX i) hγ).smul_const _
  exact hsum.congr_of_eventuallyEq heq
    (by rw [sectionCoord_apply]
        exact continuousLinearMapAt_eq_sum_localFrameCoeff (Module.finBasis 𝕜 E) hx)

/-- The coordinate reading of a vector field restricted to a curve is differentiable.  This is the
side condition under which the algebra laws of `AlongCurve/Basic.lean` apply to such a field. -/
theorem differentiableWithinAt_sectionCoord_comp_vectorField
    (hX : MDifferentiableAt I (I.prod 𝓘(𝕜, E)) (fun y ↦ TotalSpace.mk' E y (X y)) (γ t))
    (hγ : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w)) :
    DifferentiableWithinAt 𝕜 (sectionCoord (F := E) γ (fun r ↦ X (γ r)) (γ t)) s t :=
  (hasDerivWithinAt_sectionCoord_comp_vectorField hX hγ).differentiableWithinAt

/-- **The along-curve derivative of a restricted vector field is the ambient covariant
derivative.** If `X` is a tangent vector field on `M`, differentiable at `γ t`, and the curve `γ`
has velocity `w` at `t` within a parameter set with the unique-differentiability property, then
the moving-chart along-curve derivative of `fun r ↦ X (γ r)` at `t` is `∇_w X`.

Together with the algebra and locality laws of `AlongCurve/Basic.lean` this is do Carmo's
characterization of covariant differentiation along a curve, and it shows that the moving-chart
formula computes a chart-independent object on the fields it can be tested against. -/
theorem alongCurveWithin_comp_vectorField
    (hX : MDifferentiableAt I (I.prod 𝓘(𝕜, E)) (fun y ↦ TotalSpace.mk' E y (X y)) (γ t))
    (hγ : HasMFDerivWithinAt 𝓘(𝕜, 𝕜) I γ s t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w))
    (hs : UniqueDiffWithinAt 𝕜 s t) :
    alongCurveWithin cov γ (fun r ↦ X (γ r)) s t = cov X (γ t) w := by
  have hx : γ t ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  -- The three ingredients of the coordinate formula, read in the chart at `γ t` itself.
  have hu : derivWithin (extChartAt I (γ t) ∘ γ) s t = w :=
    (hasDerivWithinAt_extChartAt_comp_curve hγ).derivWithin hs
  have hv : sectionCoord (F := E) γ (fun r ↦ X (γ r)) (γ t) t = X (γ t) := by
    rw [sectionCoord_apply]
    exact continuousLinearMapAt_trivializationAt_self (γ t) (X (γ t))
  have hflat : derivWithin (sectionCoord (F := E) γ (fun r ↦ X (γ r)) (γ t)) s t
      = frameCovariantDerivative I (Module.finBasis 𝕜 E)
          (trivializationAt E (TangentSpace I) (γ t)) X (γ t) w := by
    rw [(hasDerivWithinAt_sectionCoord_comp_vectorField hX hγ).derivWithin hs,
      frameCovariantDerivative_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [localFrame_trivializationAt_self]
    rfl
  rw [alongCurveWithin_apply, alongCurveInChartWithin_apply,
    symmL_trivializationAt_self, hflat, hv, hu,
    covariantDerivative_eq_add_christoffelForm (Module.finBasis 𝕜 E)
      (cov.isCovariantDerivativeOn) hx hX, add_apply]
  congr 1
  -- Over its own base point the trivialization is the identity, so the model-space Christoffel
  -- map is the Christoffel form itself.  The two sides are stated in `E` and in the tangent space
  -- at `γ t`, so the identification is made by a typed auxiliary statement.
  have hCM : ∀ v u : E, christoffelMap (Module.finBasis 𝕜 E)
      (cov.isCovariantDerivativeOn
        (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ t) v u
      = christoffelForm (Module.finBasis 𝕜 E)
        (cov.isCovariantDerivativeOn
          (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ t) v u := by
    intro v u
    rw [christoffelMap_apply (Module.finBasis 𝕜 E) (cov.isCovariantDerivativeOn) hx,
      symmL_trivializationAt_self, symmL_trivializationAt_self,
      continuousLinearMapAt_trivializationAt_self]
  exact hCM (X (γ t)) w

/-- The unrestricted case of `CovariantDerivative.alongCurveWithin_comp_vectorField`. -/
theorem alongCurve_comp_vectorField
    (hX : MDifferentiableAt I (I.prod 𝓘(𝕜, E)) (fun y ↦ TotalSpace.mk' E y (X y)) (γ t))
    (hγ : HasMFDerivAt 𝓘(𝕜, 𝕜) I γ t ((1 : 𝕜 →L[𝕜] 𝕜).smulRight w)) :
    alongCurve cov γ (fun r ↦ X (γ r)) t = cov X (γ t) w := by
  rw [← alongCurveWithin_univ]
  exact alongCurveWithin_comp_vectorField cov hX hγ.hasMFDerivWithinAt uniqueDiffWithinAt_univ

end CovariantDerivative
