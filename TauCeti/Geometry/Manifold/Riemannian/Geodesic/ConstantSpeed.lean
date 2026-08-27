/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Reparametrization
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

/-!
# Constant speed of geodesics

A geodesic has constant speed on every open preconnected parameter set. We first prove that the
inner product of its velocity with itself is constant, by differentiating it with the
metric-product rule and using the geodesic equation. Taking square roots gives the usual
constant-speed statement.

The open-set formulation is the one used by maximal integral curves, whose parameter domains are
open intervals. It also yields an all-time specialization directly.

## Main results

* TauCeti.Manifold.IsGeodesicCurveOn.inner_curveVelocity_eq: squared speed is constant on an
  open preconnected parameter set.
* TauCeti.Manifold.IsGeodesicCurveOn.norm_curveVelocity_eq: speed is constant there.
* TauCeti.Manifold.IsGeodesicCurve.norm_curveVelocity_eq: an all-time geodesic has the same
  speed at any two parameters.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Constant speed".
* M. P. do Carmo, Riemannian Geometry, Chapter 3, §2.
* The proof follows the organization of
  DoCarmoLib/Riemannian/Geodesic/HopfRinow/ConstantSpeed.lean in the Apache-2.0
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

/-- The coordinate reading of the unrestricted velocity of a C² curve is differentiable at
each point of an open parameter set. -/
private theorem IsGeodesicCurveOn.differentiableAt_sectionCoord_curveVelocity
    (h : IsGeodesicCurveOn I γ s) (hs : IsOpen s) {t : ℝ} (ht : t ∈ s) :
    DifferentiableAt ℝ
      (sectionCoord (F := E) γ (curveVelocity I γ) (γ t)) t := by
  let _ : IsManifold I ((1 : ℕ∞ω) + 1) M := IsManifold.of_le (n := 2) (by norm_num)
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ((1 : ℕ∞ω) + 1) γ s := by
    norm_num
    exact h.contMDiffOn
  have hwithin := (contDiffWithinAt_sectionCoord_curveVelocityWithin γ h.uniqueDiffOn hγ ht
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))).differentiableWithinAt
      (by norm_num)
  have hdiff : DifferentiableAt ℝ
      (sectionCoord (F := E) γ (curveVelocityWithin I γ s) (γ t)) t :=
    hwithin.differentiableAt (hs.mem_nhds ht)
  have heq : sectionCoord (F := E) γ (curveVelocityWithin I γ s) (γ t) =ᶠ[𝓝 t]
      sectionCoord (F := E) γ (curveVelocity I γ) (γ t) := by
    filter_upwards [hs.mem_nhds ht] with r hr
    rw [sectionCoord_apply, sectionCoord_apply,
      curveVelocityWithin_of_mem_nhds (hs.mem_nhds hr)]
  exact heq.differentiableAt_iff.mp hdiff

/-- Squared speed is constant along a geodesic. On an open preconnected parameter set, the
inner product of the velocity with itself has the same value at every two parameters. -/
theorem IsGeodesicCurveOn.inner_curveVelocity_eq
    (h : IsGeodesicCurveOn I γ s) (hs : IsOpen s) (hconn : IsPreconnected s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    inner ℝ (curveVelocity I γ a) (curveVelocity I γ a) =
      inner ℝ (curveVelocity I γ b) (curveVelocity I γ b) := by
  have hzero := (isGeodesicCurveOn_iff_of_isOpen hs).mp h |>.2
  have hmetric := (isLeviCivita_leviCivita (I := I) (M := M)).isMetricCompatible
  apply hs.is_const_of_deriv_eq_zero (f := fun t ↦
    inner ℝ (curveVelocity I γ t) (curveVelocity I γ t)) hconn
  · intro t ht
    have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
      (h.contMDiffOn.contMDiffAt (hs.mem_nhds ht)).mdifferentiableAt (by norm_num)
    exact (hmetric.differentiableAt_inner_alongCurve hγt
      (h.differentiableAt_sectionCoord_curveVelocity hs ht)
      (h.differentiableAt_sectionCoord_curveVelocity hs ht)).differentiableWithinAt
  · intro t ht
    have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
      (h.contMDiffOn.contMDiffAt (hs.mem_nhds ht)).mdifferentiableAt (by norm_num)
    rw [hmetric.deriv_inner_alongCurve hγt
      (h.differentiableAt_sectionCoord_curveVelocity hs ht)
      (h.differentiableAt_sectionCoord_curveVelocity hs ht), hzero t ht]
    simp
  · exact ha
  · exact hb

/-- A geodesic has constant speed. On an open preconnected parameter set, the norm of its
velocity has the same value at every two parameters. -/
theorem IsGeodesicCurveOn.norm_curveVelocity_eq
    (h : IsGeodesicCurveOn I γ s) (hs : IsOpen s) (hconn : IsPreconnected s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    ‖curveVelocity I γ a‖ = ‖curveVelocity I γ b‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    h.inner_curveVelocity_eq hs hconn ha hb]

/-- An all-time geodesic has the same squared speed at every two parameters. -/
theorem IsGeodesicCurve.inner_curveVelocity_eq
    (h : IsGeodesicCurve I γ) (a b : ℝ) :
    inner ℝ (curveVelocity I γ a) (curveVelocity I γ a) =
      inner ℝ (curveVelocity I γ b) (curveVelocity I γ b) :=
  IsGeodesicCurveOn.inner_curveVelocity_eq
    ((isGeodesicCurveOn_univ (I := I) (γ := γ)).mpr h) isOpen_univ isPreconnected_univ
    (Set.mem_univ a) (Set.mem_univ b)

/-- An all-time geodesic has the same speed at every two parameters. -/
theorem IsGeodesicCurve.norm_curveVelocity_eq
    (h : IsGeodesicCurve I γ) (a b : ℝ) :
    ‖curveVelocity I γ a‖ = ‖curveVelocity I γ b‖ :=
  IsGeodesicCurveOn.norm_curveVelocity_eq
    ((isGeodesicCurveOn_univ (I := I) (γ := γ)).mpr h) isOpen_univ isPreconnected_univ
    (Set.mem_univ a) (Set.mem_univ b)

end TauCeti.Manifold

end
