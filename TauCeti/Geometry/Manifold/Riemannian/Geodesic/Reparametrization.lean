/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic

/-!
# Restriction and affine reparametrization of geodesics

A geodesic remains a geodesic after restricting its parameter set, provided the smaller set still
has unique derivatives. It also remains a geodesic after an affine change of parameter
`t ↦ a * t + b`. The latter statement is special to affine reparametrizations: the velocity gains
one factor of `a`, and its covariant derivative gains a second factor, with no acceleration term
from the reparametrization.

The proofs use the naturality of `CovariantDerivative.alongCurveWithin` and the `C¹` regularity of
the coordinate reading of the velocity of a `C²` curve. Every domain condition is explicit:
restriction needs an inclusion of parameter sets, while reparametrization needs the affine map to
carry the new parameter set into the old one. Restriction is the case `a = 1`, `b = 0` of the
affine statement.

The same two operations are recorded for geodesics carrying prescribed initial data: restriction
to a parameter set still containing `0` keeps the initial data, and the scaling `t ↦ a * t`, which
fixes `0`, keeps the initial point and multiplies the initial velocity by `a`.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.comp_affine`: precompose a geodesic with
  `t ↦ a * t + b`.
* `TauCeti.Manifold.IsGeodesicCurveOn.mono`: restrict a geodesic to a smaller parameter set.
* `TauCeti.Manifold.IsGeodesicCurve.comp_affine`: the all-time specialization.
* `TauCeti.Manifold.IsGeodesicCurveOnFrom.mono` and
  `TauCeti.Manifold.IsGeodesicCurveOnFrom.comp_mul_left`: the two operations on a geodesic with
  prescribed initial data.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 3, Section 2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Chapter 4, Problem 4-10.
* The reparametrization argument follows `ParallelReparametrization.lean` in the Apache-2.0
  [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`, adapted to Tau Ceti's
  interval-aware geodesic and along-curve APIs.
* [The Hopf--Rinow roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Maximal interval and homogeneity".
-/

public section

open Bundle CovariantDerivative Filter Set
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
  {γ : ℝ → M} {s u : Set ℝ} {p : M} {v : TangentSpace I p}

/-- A geodesic remains a geodesic after the affine reparametrization `t ↦ a * t + b`, provided
that map carries the new parameter set into the original one. The case `a = 0` is included and
gives a constant curve. -/
theorem IsGeodesicCurveOn.comp_affine (h : IsGeodesicCurveOn I γ s) (a b : ℝ)
    (hu : UniqueDiffOn ℝ u) (hmaps : MapsTo (fun t : ℝ ↦ a * t + b) u s) :
    IsGeodesicCurveOn I (γ ∘ fun t : ℝ ↦ a * t + b) u where
  uniqueDiffOn := hu
  contMDiffOn := by
    have hφ : ContDiff ℝ 2 (fun t : ℝ ↦ a * t + b) := by fun_prop
    exact h.contMDiffOn.comp hφ.contMDiff.contMDiffOn hmaps
  alongCurveWithin_curveVelocityWithin_eq_zero t ht := by
    let φ : ℝ → ℝ := fun r ↦ a * r + b
    have hφ (r : ℝ) : HasDerivWithinAt φ a u r :=
      ((hasDerivAt_const_mul a).add_const b).hasDerivWithinAt
    have hchart : DifferentiableWithinAt ℝ (extChartAt I (γ (φ t)) ∘ γ) s (φ t) :=
      (hasDerivWithinAt_extChartAt_comp_curve (hasMFDerivWithinAt_curveVelocityWithin
        (h.mdifferentiableOn (φ t) (hmaps ht)))).differentiableWithinAt
    have hsection : DifferentiableWithinAt ℝ
        (sectionCoord (F := E) γ (curveVelocityWithin I γ s) (γ (φ t))) s (φ t) := by
      let _ : IsManifold I ((1 : ℕ∞ω) + 1) M := IsManifold.of_le (n := 2) (by norm_num)
      have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ((1 : ℕ∞ω) + 1) γ s := by
        norm_num
        exact h.contMDiffOn
      exact (contDiffWithinAt_sectionCoord_curveVelocityWithin γ h.uniqueDiffOn hγ (hmaps ht)
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I)
          (γ (φ t)))).differentiableWithinAt (by norm_num)
    have hvelocity (r : ℝ) (hr : r ∈ u) :
        curveVelocityWithin I (γ ∘ φ) u r =
          a • curveVelocityWithin I γ s (φ r) :=
      curveVelocityWithin_comp (hφ r) hmaps (h.mdifferentiableOn (φ r) (hmaps hr)) (hu r hr)
    have hvelocity_eventually :
        curveVelocityWithin I (γ ∘ φ) u =ᶠ[𝓝[u] t]
          fun r ↦ a • curveVelocityWithin I γ s (φ r) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact hvelocity r hr
    have hreparam :
        alongCurveWithin (leviCivita I M) (γ ∘ φ)
            (fun r ↦ curveVelocityWithin I γ s (φ r)) u t =
          a • alongCurveWithin (leviCivita I M) γ (curveVelocityWithin I γ s) s (φ t) := by
      rw [alongCurveWithin_comp (leviCivita I M) γ (curveVelocityWithin I γ s) φ
        (hφ t).differentiableWithinAt hmaps hchart hsection, (hφ t).derivWithin (hu t ht)]
    calc
      alongCurveWithin (leviCivita I M) (γ ∘ φ)
          (curveVelocityWithin I (γ ∘ φ) u) u t =
          alongCurveWithin (leviCivita I M) (γ ∘ φ)
            (fun r ↦ a • curveVelocityWithin I γ s (φ r)) u t :=
        alongCurveWithin_congr (leviCivita I M) (γ ∘ φ) _ hvelocity_eventually
          (hvelocity t ht)
      _ = a • alongCurveWithin (leviCivita I M) (γ ∘ φ)
          (fun r ↦ curveVelocityWithin I γ s (φ r)) u t :=
        alongCurveWithin_const_smul (leviCivita I M) (γ ∘ φ)
          (fun r ↦ curveVelocityWithin I γ s (φ r)) a u t
      _ = a • (a • alongCurveWithin (leviCivita I M) γ
          (curveVelocityWithin I γ s) s (φ t)) := by rw [hreparam]
      _ = 0 := by rw [h.alongCurveWithin_curveVelocityWithin_eq_zero (φ t) (hmaps ht)]; simp

/-- A geodesic remains a geodesic after restriction to a smaller parameter set with unique
derivatives. The smaller set need not be open or an interval. -/
theorem IsGeodesicCurveOn.mono (h : IsGeodesicCurveOn I γ s) (hu : UniqueDiffOn ℝ u)
    (hus : u ⊆ s) : IsGeodesicCurveOn I γ u := by
  simpa [Function.comp_def] using h.comp_affine 1 0 hu (fun t ht ↦ by simpa using hus ht)

/-- An all-time geodesic remains an all-time geodesic after an affine reparametrization. -/
theorem IsGeodesicCurve.comp_affine (h : IsGeodesicCurve I γ) (a b : ℝ) :
    IsGeodesicCurve I (γ ∘ fun t : ℝ ↦ a * t + b) := by
  rw [← isGeodesicCurveOn_univ] at h ⊢
  exact h.comp_affine a b uniqueDiffOn_univ (mapsTo_univ _ _)

/-- A geodesic with prescribed initial data keeps that data after restriction to a smaller
parameter set with unique derivatives which still contains the initial parameter `0`. -/
theorem IsGeodesicCurveOnFrom.mono (h : IsGeodesicCurveOnFrom I γ s p v) (hu : UniqueDiffOn ℝ u)
    (hus : u ⊆ s) (h0 : (0 : ℝ) ∈ u) : IsGeodesicCurveOnFrom I γ u p v where
  isGeodesicCurveOn := h.isGeodesicCurveOn.mono hu hus
  zero_mem := h0
  initial_eq := by
    rw [curveVelocityWithin_subset hus (hu 0 h0)
      (h.isGeodesicCurveOn.mdifferentiableOn 0 (hus h0))]
    exact h.initial_eq

/-- The reparametrization `t ↦ a * t` fixes the initial parameter `0`, so a geodesic with
prescribed initial data keeps its initial point and has its initial velocity multiplied by `a`. -/
theorem IsGeodesicCurveOnFrom.comp_mul_left (h : IsGeodesicCurveOnFrom I γ s p v) (a : ℝ)
    (hu : UniqueDiffOn ℝ u) (hmaps : MapsTo (fun t : ℝ ↦ a * t) u s) (h0 : (0 : ℝ) ∈ u) :
    IsGeodesicCurveOnFrom I (γ ∘ fun t : ℝ ↦ a * t) u p (a • v) where
  isGeodesicCurveOn := by
    simpa using h.isGeodesicCurveOn.comp_affine a 0 hu (fun t ht ↦ by simpa using hmaps ht)
  zero_mem := h0
  initial_eq := by
    rw [curveVelocityWithin_comp (hasDerivAt_const_mul a).hasDerivWithinAt hmaps
      (h.isGeodesicCurveOn.mdifferentiableOn _ (hmaps h0)) (hu 0 h0)]
    rw [Function.comp_apply, mul_zero]
    -- Scaling the fibre component by `a` is a map of the tangent bundle, so it can be applied
    -- to the bundled initial data of `h`.
    exact congrArg (fun z : TangentBundle I M ↦ TotalSpace.mk' E z.proj (a • z.snd)) h.initial_eq

end TauCeti.Manifold

end
