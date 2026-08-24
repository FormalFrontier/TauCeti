/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Existence

/-!
# The Levi-Civita covariant derivative along a curve

This file specializes the generic along-curve construction to the canonical Levi-Civita
connection of the supplied Riemannian bundle instance.  The connection is deliberately not an
explicit argument: this is the metric convention used by the geodesic and exponential-map API.

For a curve `γ : ℝ → M` and a tangent field `V : ∀ t, TangentSpace I (γ t)`,
`covariantDerivativeAlong γ V t` is the tangent vector `D V / dt` at `γ t`.  The additive,
Leibniz, locality, and reparametrization laws are inherited from the generic construction.

## Main definitions and results

* `TauCeti.Riemannian.covariantDerivativeAlong`: covariant differentiation along a curve for the
  canonical Levi-Civita connection.
* `TauCeti.Riemannian.covariantDerivativeAlong_add` and
  `TauCeti.Riemannian.covariantDerivativeAlong_smul`: its characteristic algebra laws.
* `TauCeti.Riemannian.covariantDerivativeAlong_congr`: locality in the tangent field.
* `TauCeti.Riemannian.covariantDerivativeAlong_comp`: naturality under reparametrization.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Covariant derivative along a curve".
* M. P. do Carmo, *Riemannian Geometry*, Birkhauser, 1992, Ch. 2, Proposition 2.2.
-/

public section

open Bundle Filter
open scoped Manifold Topology

noncomputable section

namespace TauCeti.Riemannian

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

variable (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))

/-- The Levi-Civita covariant derivative of a tangent field `V` along a curve `γ`. -/
def covariantDerivativeAlong (t : ℝ) : TangentSpace I (γ t) :=
  CovariantDerivative.alongCurve
    (CovariantDerivative.leviCivita I M) γ V t

/-- The canonical along-curve derivative is the generic construction for the Levi-Civita
connection. -/
@[simp]
theorem covariantDerivativeAlong_apply (t : ℝ) :
    covariantDerivativeAlong γ V t =
      CovariantDerivative.alongCurve
        (CovariantDerivative.leviCivita I M) γ V t :=
  (rfl)

/-- The Levi-Civita covariant derivative along a curve is additive in the tangent field. -/
theorem covariantDerivativeAlong_add (W : ∀ t, TangentSpace I (γ t)) {t : ℝ}
    (hV : DifferentiableAt ℝ
      (CovariantDerivative.tangentFieldCoord γ V (γ t)) t)
    (hW : DifferentiableAt ℝ
      (CovariantDerivative.tangentFieldCoord γ W (γ t)) t) :
    covariantDerivativeAlong γ (fun s ↦ V s + W s) t =
      covariantDerivativeAlong γ V t + covariantDerivativeAlong γ W t := by
  simp only [covariantDerivativeAlong_apply]
  exact CovariantDerivative.alongCurve_add
    (CovariantDerivative.leviCivita I M) γ V W hV hW

/-- The Levi-Civita covariant derivative along a curve obeys the scalar Leibniz rule. -/
theorem covariantDerivativeAlong_smul (f : ℝ → ℝ) {t : ℝ} (hf : DifferentiableAt ℝ f t)
    (hV : DifferentiableAt ℝ
      (CovariantDerivative.tangentFieldCoord γ V (γ t)) t) :
    covariantDerivativeAlong γ (fun s ↦ f s • V s) t =
      deriv f t • V t + f t • covariantDerivativeAlong γ V t := by
  simp only [covariantDerivativeAlong_apply]
  exact CovariantDerivative.alongCurve_smul
    (CovariantDerivative.leviCivita I M) γ V f hf hV

/-- The Levi-Civita covariant derivative of the zero field along a curve is zero. -/
theorem covariantDerivativeAlong_zero (t : ℝ) :
    covariantDerivativeAlong γ (fun s : ℝ ↦ (0 : TangentSpace I (γ s))) t = 0 := by
  simp only [covariantDerivativeAlong_apply]
  exact CovariantDerivative.alongCurve_zero
    (CovariantDerivative.leviCivita I M) γ t

/-- The Levi-Civita covariant derivative along a curve depends only on the germ of the tangent
field at the parameter under consideration. -/
theorem covariantDerivativeAlong_congr {W : ∀ t, TangentSpace I (γ t)} {t : ℝ}
    (h : V =ᶠ[𝓝 t] W) :
    covariantDerivativeAlong γ V t = covariantDerivativeAlong γ W t := by
  simp only [covariantDerivativeAlong_apply]
  exact CovariantDerivative.alongCurve_congr
    (CovariantDerivative.leviCivita I M) γ V h

/-- The Levi-Civita covariant derivative along a curve is natural under differentiable
reparametrization. -/
theorem covariantDerivativeAlong_comp (φ : ℝ → ℝ) {t : ℝ} (hφ : DifferentiableAt ℝ φ t)
    (hγ : DifferentiableAt ℝ
      (CovariantDerivative.curveCoord (I := I) γ (γ (φ t))) (φ t))
    (hV : DifferentiableAt ℝ
      (CovariantDerivative.tangentFieldCoord γ V (γ (φ t))) (φ t)) :
    covariantDerivativeAlong (γ ∘ φ) (fun s ↦ V (φ s)) t =
      deriv φ t • covariantDerivativeAlong γ V (φ t) := by
  simp only [covariantDerivativeAlong_apply]
  exact CovariantDerivative.alongCurve_comp
    (CovariantDerivative.leviCivita I M) γ V φ hφ hγ hV

end TauCeti.Riemannian
