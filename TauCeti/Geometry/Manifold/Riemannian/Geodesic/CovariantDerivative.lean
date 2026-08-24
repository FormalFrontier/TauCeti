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
explicit argument: this is the metric convention the geodesic and exponential-map API will use.

For a curve `γ : ℝ → M` and a tangent field `V : ∀ t, TangentSpace I (γ t)`,
`covariantDerivativeAlong γ V t` is the tangent vector `D V / dt` at `γ t`.  Its defining formula
and all of its laws are those of `CovariantDerivative.alongCurve`, reached through
`TauCeti.Manifold.covariantDerivativeAlong_def`.

## Main definitions and results

* `TauCeti.Manifold.covariantDerivativeAlong`: covariant differentiation along a curve for the
  canonical Levi-Civita connection, with
  `TauCeti.Manifold.covariantDerivativeAlong_def` identifying it with the generic construction.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Covariant derivative along a curve".
* M. P. do Carmo, *Riemannian Geometry*, Birkhauser, 1992, Ch. 2, Proposition 2.2.
-/

public section

open Bundle
open scoped Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

variable (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))

/-- The Levi-Civita covariant derivative of a tangent field `V` along a curve `γ`: the generic
along-curve derivative `CovariantDerivative.alongCurve` for the canonical Levi-Civita connection,
and so with the same junk values and the same fixed local frame. -/
def covariantDerivativeAlong (t : ℝ) : TangentSpace I (γ t) :=
  CovariantDerivative.alongCurve
    (CovariantDerivative.leviCivita I M) γ V t

/-- The canonical along-curve derivative is the generic construction for the Levi-Civita
connection. -/
theorem covariantDerivativeAlong_def (t : ℝ) :
    covariantDerivativeAlong γ V t =
      CovariantDerivative.alongCurve
        (CovariantDerivative.leviCivita I M) γ V t :=
  (rfl)

end TauCeti.Manifold
