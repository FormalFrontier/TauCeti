/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Coordinate displacement is bounded by Riemannian path length

This file supplies the local analytic bridge from a Riemannian path to its expression in a
coordinate chart.  If the chart derivative is bounded along a `C¹` path, the coordinate
displacement of the path is bounded by that derivative bound times its Riemannian length.

This is the chart-level estimate needed when transferring vector-valued variation estimates to
`Manifold.pathELength` in the Hopf--Rinow lower-semicontinuity argument.  The proof uses the
interval-integral estimate
`enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc` and the chain rule for `mfderivWithin`.

The interval-integral estimate and the local-coordinate differential argument follow the
corresponding constructions in Mathlib's `Geometry/Manifold/Riemannian/Basic.lean`.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 0, "Regular reparametrization and limits".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7 §2.
-/

public section

open Bundle Manifold MeasureTheory Set
open scoped Bundle ENNReal Manifold NNReal Topology

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

namespace Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]

local instance normedAddCommGroupTangentSpaceVectorSpace (x : E) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedAddCommGroup E)

local instance normedSpaceTangentSpaceVectorSpace (x : E) :
    NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedSpace ℝ E)

/-- A bound on the chart derivative controls the coordinate displacement of a smooth path. -/
theorem enorm_extChartAt_sub_le_mul_pathELength (x : M) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : CMDiff[Icc a b] 1 γ)
    (hγsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H x).source)
    {C : ℝ≥0} (hC : ∀ t ∈ Icc a b, ∀ v,
      ‖(mfderiv% (extChartAt I x) (γ t)) v‖ₑ ≤ C * ‖v‖ₑ) :
    ‖extChartAt I x (γ b) - extChartAt I x (γ a)‖ₑ ≤ C * pathELength I γ a b := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let γ' := extChartAt I x ∘ γ
  have hγ' : CMDiff[Icc a b] 1 γ' := by
    exact contMDiffOn_extChartAt.comp (I' := I) (t := (chartAt H x).source)
      hγ (fun t ht ↦ hγsrc t ht)
  have hbound : ‖γ' b - γ' a‖ₑ ≤ C * pathELength I γ a b := by
    calc
      ‖γ' b - γ' a‖ₑ ≤
          ∫⁻ t in Icc a b, ‖derivWithin γ' (Icc a b) t‖ₑ := by
        apply enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc _ hab.le
        rwa [← contMDiffOn_iff_contDiffOn]
      _ = ∫⁻ t in Icc a b, ‖mfderiv[Icc a b] γ' t 1‖ₑ := by
        simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
        rfl
      _ ≤ ∫⁻ t in Icc a b, C * ‖mfderiv[Icc a b] γ t 1‖ₑ := by
        apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
        have hderiv : mfderiv[Icc a b] γ' t =
            (mfderiv% (extChartAt I x) (γ t)) ∘L (mfderiv[Icc a b] γ t) := by
          apply mfderiv_comp_mfderivWithin
          · exact mdifferentiableAt_extChartAt (hγsrc t ht)
          · exact (hγ t ht).mdifferentiableWithinAt one_ne_zero
          · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact uniqueDiffOn_Icc hab _ ht
        have hderiv_apply : mfderiv[Icc a b] γ' t 1 =
            (mfderiv% (extChartAt I x) (γ t)) (mfderiv[Icc a b] γ t 1) :=
          congr($hderiv 1)
        rw [hderiv_apply]
        exact hC t ht (mfderiv[Icc a b] γ t 1)
      _ = C * pathELength I γ a b := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          pathELength_eq_lintegral_mfderivWithin_Icc]
  simpa [γ'] using hbound

end Manifold
end TauCeti
