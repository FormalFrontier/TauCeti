/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Covariant differentiation along a curve

This file constructs the covariant derivative of a tangent field along a curve.  At a parameter
`t`, both the curve and the field are read in the tangent-bundle trivialization coming from the
chart centred at the current point `γ t`.  If `u` and `v` are those coordinate readings and `Γ`
is the Christoffel map of the connection in that frame, the defining formula is

`D V / dt = v' + Γ(v, u')`.

The result is transported back to `TangentSpace I (γ t)`.  Thus the definition uses the chart at
the current point rather than a single global chart.  This first part of the along-curve API proves
the characteristic additive and scalar Leibniz laws, locality in the field, and naturality under
differentiable reparametrization.  A subsequent file will identify the formula in an arbitrary
fixed chart and compare it with the ambient covariant derivative of a pulled-back vector field.

## Main definitions and results

* `TauCeti.CovariantDerivative.tangentFieldCoord`: the coordinate reading of a tangent field along
  a curve in a specified tangent-bundle trivialization.
* `TauCeti.CovariantDerivative.alongCurveInChart`: the model-space formula `v' + Γ(v, u')`.
* `TauCeti.CovariantDerivative.alongCurve`: the resulting tangent field along the curve.
* `TauCeti.CovariantDerivative.alongCurve_add` and
  `TauCeti.CovariantDerivative.alongCurve_smul`: additivity and the scalar Leibniz rule.
* `TauCeti.CovariantDerivative.alongCurve_congr` and
  `TauCeti.CovariantDerivative.alongCurve_comp`: locality and reparametrization.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Covariant derivative along a curve".
* M. P. do Carmo, *Riemannian Geometry*, Birkhauser, 1992, Ch. 2, Proposition 2.2.
* The moving-chart construction was informed by `CovariantDerivativeAlong.lean` and
  `AffineCovariantDerivativeAlong.lean` in the Apache-2.0
  [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture) repository
  at revision `4dff1831c65f51855a70dc3c4ff03bea49a5619e`; this implementation instead uses Mathlib's
  `CovariantDerivative` and Tau Ceti's `christoffelMap` directly.
-/

public section

open Bundle Filter
open scoped Manifold Topology

noncomputable section

namespace TauCeti.CovariantDerivative

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

variable (cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  (γ : 𝕜 → M) (V : ∀ t, TangentSpace I (γ t))

/-- The model-space reading of a tangent field `V` along `γ` in the tangent-bundle
trivialization centred at `x`.  The continuous linear map is defined everywhere (with Mathlib's
junk value outside the chart), while all derivative results use it only near a point where the
curve lies in the chart. -/
def tangentFieldCoord (x : M) (t : 𝕜) : E :=
  (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 (γ t) (V t)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The defining formula for the coordinate reading of a tangent field. -/
@[simp]
theorem tangentFieldCoord_apply (x : M) (t : 𝕜) :
    tangentFieldCoord γ V x t =
      (trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 (γ t) (V t) :=
  (rfl)

/-- The model-space reading of a curve in the extended chart centred at `x`. -/
def curveCoord (x : M) (t : 𝕜) : E :=
  extChartAt I x (γ t)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The defining formula for the coordinate reading of a curve. -/
@[simp]
theorem curveCoord_apply (x : M) (t : 𝕜) :
    curveCoord (I := I) γ x t = extChartAt I x (γ t) :=
  (rfl)

/-- The coordinate covariant derivative of `V` along `γ` in the chart centred at `x`:
`v' + Γ(v, u')`, where `u` and `v` are the coordinate readings of the curve and field. -/
def alongCurveInChart (x : M) (t : 𝕜) : E :=
  let e := trivializationAt E (TangentSpace I) x
  deriv (tangentFieldCoord γ V x) t +
    TauCeti.Manifold.christoffelMap (Module.finBasis 𝕜 E)
      (cov.isCovariantDerivativeOn (s := e.baseSet)) (γ t)
        (tangentFieldCoord γ V x t) (deriv (curveCoord (I := I) γ x) t)

/-- The covariant derivative of `V` along `γ`, computed in the chart centred at the current point
and transported back from the model space to `TangentSpace I (γ t)`. -/
def alongCurve (t : 𝕜) : TangentSpace I (γ t) :=
  (trivializationAt E (TangentSpace I) (γ t)).symmL 𝕜 (γ t)
    (alongCurveInChart cov γ V (γ t) t)

/-! ### Coordinate-field operations -/

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- Coordinate reading commutes with pointwise addition of fields along a curve. -/
theorem tangentFieldCoord_add (W : ∀ t, TangentSpace I (γ t)) (x : M) :
    tangentFieldCoord γ (fun t ↦ V t + W t) x =
      tangentFieldCoord γ V x + tangentFieldCoord γ W x := by
  funext t
  exact map_add _ _ _

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- Coordinate reading commutes with pointwise scalar multiplication of a field along a curve. -/
theorem tangentFieldCoord_smul (f : 𝕜 → 𝕜) (x : M) :
    tangentFieldCoord γ (fun t ↦ f t • V t) x = f • tangentFieldCoord γ V x := by
  funext t
  exact map_smul _ _ _

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The zero tangent field has zero coordinate reading. -/
@[simp]
theorem tangentFieldCoord_zero (x : M) :
    tangentFieldCoord γ (fun t : 𝕜 ↦ (0 : TangentSpace I (γ t))) x = (0 : 𝕜 → E) := by
  funext t
  exact map_zero _

/-! ### Algebra laws -/

/-- The coordinate covariant derivative is additive in the field. -/
theorem alongCurveInChart_add (W : ∀ t, TangentSpace I (γ t)) (x : M) {t : 𝕜}
    (hV : DifferentiableAt 𝕜 (tangentFieldCoord γ V x) t)
    (hW : DifferentiableAt 𝕜 (tangentFieldCoord γ W x) t) :
    alongCurveInChart cov γ (fun s ↦ V s + W s) x t =
      alongCurveInChart cov γ V x t + alongCurveInChart cov γ W x t := by
  rw [alongCurveInChart, alongCurveInChart, alongCurveInChart, tangentFieldCoord_add,
    deriv_add hV hW]
  simp only [Pi.add_apply, map_add, add_apply]
  abel

/-- Covariant differentiation along a curve is additive in the field. -/
theorem alongCurve_add (W : ∀ t, TangentSpace I (γ t)) {t : 𝕜}
    (hV : DifferentiableAt 𝕜 (tangentFieldCoord γ V (γ t)) t)
    (hW : DifferentiableAt 𝕜 (tangentFieldCoord γ W (γ t)) t) :
    alongCurve cov γ (fun s ↦ V s + W s) t =
      alongCurve cov γ V t + alongCurve cov γ W t := by
  rw [alongCurve, alongCurve, alongCurve, alongCurveInChart_add cov γ V W (γ t) hV hW,
    map_add]

/-- The coordinate covariant derivative obeys the scalar Leibniz rule. -/
theorem alongCurveInChart_smul (f : 𝕜 → 𝕜) (x : M) {t : 𝕜}
    (hf : DifferentiableAt 𝕜 f t)
    (hV : DifferentiableAt 𝕜 (tangentFieldCoord γ V x) t) :
    alongCurveInChart cov γ (fun s ↦ f s • V s) x t =
      deriv f t • tangentFieldCoord γ V x t + f t • alongCurveInChart cov γ V x t := by
  rw [alongCurveInChart, alongCurveInChart, tangentFieldCoord_smul,
    deriv_smul hf hV]
  simp only [Pi.smul_apply', map_smul, smul_add]
  abel

/-- Covariant differentiation along a curve obeys the scalar Leibniz rule. -/
theorem alongCurve_smul (f : 𝕜 → 𝕜) {t : 𝕜} (hf : DifferentiableAt 𝕜 f t)
    (hV : DifferentiableAt 𝕜 (tangentFieldCoord γ V (γ t)) t) :
    alongCurve cov γ (fun s ↦ f s • V s) t =
      deriv f t • V t + f t • alongCurve cov γ V t := by
  rw [alongCurve, alongCurve, alongCurveInChart_smul cov γ V f (γ t) hf hV, map_add,
    map_smul, map_smul, tangentFieldCoord_apply]
  rw [(trivializationAt E (TangentSpace I) (γ t)).symmL_continuousLinearMapAt]
  exact mem_chart_source H (γ t)

/-- The covariant derivative of the zero field along a curve is zero. -/
@[simp]
theorem alongCurve_zero (t : 𝕜) :
    alongCurve cov γ (fun s : 𝕜 ↦ (0 : TangentSpace I (γ s))) t = 0 := by
  rw [alongCurve, alongCurveInChart, tangentFieldCoord_zero (γ := γ)]
  simp

/-! ### Locality and reparametrization -/

/-- Covariant differentiation along a curve depends only on the germ of the field at the
parameter under consideration. -/
theorem alongCurve_congr {W : ∀ t, TangentSpace I (γ t)} {t : 𝕜}
    (h : V =ᶠ[𝓝 t] W) : alongCurve cov γ V t = alongCurve cov γ W t := by
  have hcoord : tangentFieldCoord γ V (γ t) =ᶠ[𝓝 t]
      tangentFieldCoord γ W (γ t) := h.mono fun s hs ↦ by
    simp only [tangentFieldCoord_apply, hs]
  rw [alongCurve, alongCurve, alongCurveInChart, alongCurveInChart,
    hcoord.deriv_eq, hcoord.self_of_nhds]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The coordinate readings of a reparametrized curve and field are compositions with the
reparametrizing function. -/
theorem tangentFieldCoord_comp (φ : 𝕜 → 𝕜) (x : M) :
    tangentFieldCoord (γ ∘ φ) (fun t ↦ V (φ t)) x = tangentFieldCoord γ V x ∘ φ := by
  ext t
  simp only [tangentFieldCoord_apply, Function.comp_apply]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The coordinate reading of a reparametrized curve is a composition with the reparametrizing
function. -/
theorem curveCoord_comp (φ : 𝕜 → 𝕜) (x : M) :
    curveCoord (I := I) (γ ∘ φ) x = curveCoord (I := I) γ x ∘ φ := by
  ext t
  simp only [curveCoord_apply, Function.comp_apply]

/-- Covariant differentiation is natural under differentiable reparametrization.  Both coordinate
readings need to be differentiable at the image parameter, which is precisely the regularity used
by the two chain-rule applications. -/
theorem alongCurve_comp (φ : 𝕜 → 𝕜) {t : 𝕜} (hφ : DifferentiableAt 𝕜 φ t)
    (hγ : DifferentiableAt 𝕜 (curveCoord (I := I) γ (γ (φ t))) (φ t))
    (hV : DifferentiableAt 𝕜 (tangentFieldCoord γ V (γ (φ t))) (φ t)) :
    alongCurve cov (γ ∘ φ) (fun s ↦ V (φ s)) t =
      deriv φ t • alongCurve cov γ V (φ t) := by
  have hVcomp : deriv (tangentFieldCoord γ V (γ (φ t)) ∘ φ) t =
      deriv φ t • deriv (tangentFieldCoord γ V (γ (φ t))) (φ t) :=
    deriv.scomp t hV hφ
  have hγcomp : deriv (curveCoord (I := I) γ (γ (φ t)) ∘ φ) t =
      deriv φ t • deriv (curveCoord (I := I) γ (γ (φ t))) (φ t) :=
    deriv.scomp t hγ hφ
  rw [alongCurve, alongCurve, alongCurveInChart, alongCurveInChart,
    tangentFieldCoord_comp, curveCoord_comp]
  simp only [Function.comp_apply]
  rw [hVcomp, hγcomp, map_smul, ← smul_add, map_smul]

end TauCeti.CovariantDerivative
