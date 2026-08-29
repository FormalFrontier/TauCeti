/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

/-!
# Constant speed of geodesics

A geodesic has constant speed on every preconnected parameter set. We first prove that the inner
product of its within-set velocity with itself is constant, by differentiating it with the
within-set metric-product rule and using the geodesic equation. Taking square roots gives the usual
constant-speed statement. On an open set this velocity agrees with the unrestricted
`curveVelocity` by `curveVelocityWithin_of_mem_nhds`; the all-time specializations below are stated
directly with `curveVelocity`.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.inner_curveVelocityWithin_self_eq`: squared speed is constant
  on a preconnected parameter set.
* `TauCeti.Manifold.IsGeodesicCurveOn.norm_curveVelocityWithin_eq`: speed is constant there.
* `TauCeti.Manifold.IsGeodesicCurve.inner_curveVelocity_self_eq`: an all-time geodesic has the
  same squared speed at any two parameters.
* `TauCeti.Manifold.IsGeodesicCurve.norm_curveVelocity_eq`: an all-time geodesic has the same
  speed at any two parameters.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Constant speed".
* M. P. do Carmo, *Riemannian Geometry*, Chapter 3, §2.
* The proof follows the organization of
  `DoCarmoLib/Riemannian/Geodesic/HopfRinow/ConstantSpeed.lean` in the Apache-2.0
  [frenzymath/Poincare-Conjecture](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision 24f32e4d600878bfaac6bc2f2f9324175571c321, using Tau Ceti's
  set-aware geodesic predicate and Mathlib's Riemannian norm.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ}

/-- Squared speed is constant along a geodesic. On a preconnected parameter set, the inner product
of the within-set velocity with itself has the same value at every two parameters. On an open set
this velocity agrees with the unrestricted `curveVelocity` by
`curveVelocityWithin_of_mem_nhds`. -/
theorem IsGeodesicCurveOn.inner_curveVelocityWithin_self_eq
    (h : IsGeodesicCurveOn I γ s) (hconn : IsPreconnected s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    inner ℝ (curveVelocityWithin I γ s a) (curveVelocityWithin I γ s a) =
      inner ℝ (curveVelocityWithin I γ s b) (curveVelocityWithin I γ s b) := by
  have hmetric := (isLeviCivita_leviCivita (I := I) (M := M)).isMetricCompatible
  apply hconn.ordConnected.convex.is_const_of_fderivWithin_eq_zero
    (𝕜 := ℝ)
    (f := fun t : ℝ ↦
      inner ℝ (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t))
  · intro t ht
    have hcoord := differentiableWithinAt_sectionCoord_curveVelocityWithin γ h.uniqueDiffOn
      h.contMDiffOn ht (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
    exact hmetric.differentiableWithinAt_inner (h.uniqueDiffOn t ht)
      (h.mdifferentiableOn t ht) hcoord hcoord
  · intro t ht
    have hcoord := differentiableWithinAt_sectionCoord_curveVelocityWithin γ h.uniqueDiffOn
      h.contMDiffOn ht (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
    have hprod := hmetric.hasDerivWithinAt_inner_alongCurveWithin (h.uniqueDiffOn t ht)
      (h.mdifferentiableOn t ht) hcoord hcoord
    have hderiv : HasDerivWithinAt (fun r ↦
        inner ℝ (curveVelocityWithin I γ s r) (curveVelocityWithin I γ s r)) 0 s t :=
      hprod.congr_deriv (by
        rw [h.alongCurveWithin_curveVelocityWithin_eq_zero t ht]
        simp)
    simpa using hderiv.hasFDerivWithinAt.fderivWithin (h.uniqueDiffOn t ht)
  · exact ha
  · exact hb

/-- A geodesic has constant speed. On a preconnected parameter set, the norm of its within-set
velocity has the same value at every two parameters. On an open set this velocity agrees with the
unrestricted `curveVelocity` by `curveVelocityWithin_of_mem_nhds`. -/
theorem IsGeodesicCurveOn.norm_curveVelocityWithin_eq
    (h : IsGeodesicCurveOn I γ s) (hconn : IsPreconnected s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    ‖curveVelocityWithin I γ s a‖ = ‖curveVelocityWithin I γ s b‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    h.inner_curveVelocityWithin_self_eq hconn ha hb]

/-- An all-time geodesic has the same squared speed, expressed using the unrestricted
`curveVelocity`, at every two parameters. -/
theorem IsGeodesicCurve.inner_curveVelocity_self_eq
    (h : IsGeodesicCurve I γ) (a b : ℝ) :
    inner ℝ (curveVelocity I γ a) (curveVelocity I γ a) =
      inner ℝ (curveVelocity I γ b) (curveVelocity I γ b) := by
  simpa only [curveVelocityWithin_univ] using
    IsGeodesicCurveOn.inner_curveVelocityWithin_self_eq
      ((isGeodesicCurveOn_univ (I := I) (γ := γ)).mpr h) isPreconnected_univ
      (Set.mem_univ a) (Set.mem_univ b)

/-- An all-time geodesic has the same speed, expressed using the unrestricted `curveVelocity`, at
every two parameters. -/
theorem IsGeodesicCurve.norm_curveVelocity_eq
    (h : IsGeodesicCurve I γ) (a b : ℝ) :
    ‖curveVelocity I γ a‖ = ‖curveVelocity I γ b‖ := by
  simpa only [curveVelocityWithin_univ] using
    IsGeodesicCurveOn.norm_curveVelocityWithin_eq
      ((isGeodesicCurveOn_univ (I := I) (γ := γ)).mpr h) isPreconnected_univ
      (Set.mem_univ a) (Set.mem_univ b)

end TauCeti.Manifold

end
