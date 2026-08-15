/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import TauCeti.Geometry.Lie.Exponential.LocalInverse

/-!
# The Trotter product formula

This file proves a tangent-to-identity power limit and applies it to the product of two
exponential curves.

## Main results

* `tendsto_pow_div_of_hasDerivAt_mulInvariantLog`: a curve whose local logarithm has initial
  derivative `X` has rescaled powers converging to `exp (t X)`.
* `tendsto_mulInvariantExp_mul_pow_div`: the Trotter product formula in the tangent model.
* `tendsto_lieExp_mul_pow_div`: the Trotter product formula for left-invariant derivations.

## References

* H. Liu, *Notes for Lie Groups & Representations*, Proposition 2.4.3.
* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 2, "Closed subgroups and automatic smoothness".
-/

public section

open Filter Function Manifold
open scoped ContDiff Manifold Topology

noncomputable section

private theorem tendsto_nsmul_apply_div_of_hasDerivAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} (hf : HasDerivAt f f' 0) (hf0 : f 0 = 0) (t : ℝ) :
    Tendsto (fun n : ℕ => n • f (t / n)) atTop (nhds (t • f')) := by
  by_cases ht : t = 0
  · subst t
    simpa only [zero_div, hf0, nsmul_zero, zero_smul] using tendsto_const_nhds
  have hn : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => t / (n : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_comm, mul_zero] using hn.mul_const t
  have hs_ne : ∀ᶠ n : ℕ in (atTop : Filter ℕ), t / (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hnpos
    exact div_ne_zero ht (show (n : ℝ) ≠ 0 from
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos))
  have hs' : Tendsto (fun n : ℕ => t / (n : ℝ)) atTop
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs, hs_ne⟩
  have hscaled := (hf.tendsto_slope_zero.comp hs').const_smul t
  convert hscaled using 1
  funext n
  by_cases hn0 : n = 0
  · subst n
    simp [hf0]
  rw [show n • f (t / (n : ℝ)) = (n : ℝ) • f (t / (n : ℝ)) by
    exact (Nat.cast_smul_eq_nsmul ℝ n _).symm]
  simp only [Function.comp_apply, zero_add, hf0, sub_zero]
  rw [smul_smul]
  congr 1
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G]

attribute [local instance] LieGroup.minSmoothnessThree

/-- A tangent-to-identity curve has the expected exponential power limit. The derivative is
stated in local logarithmic coordinates so the result can be reused independently of a chosen
manifold expression for the curve. -/
theorem tendsto_pow_div_of_hasDerivAt_mulInvariantLog [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
    {f : ℝ → G} (X : GroupLieAlgebra I G) (hf0 : f 0 = 1)
    (hf : ContinuousAt f 0)
    (hlog : HasDerivAt (fun s =>
      (show E from mulInvariantLog (I := I) (G := G) (f s)))
      (show E from X) 0)
    (t : ℝ) :
    Tendsto (fun n : ℕ => (f (t / n)) ^ n) atTop
      (nhds (mulInvariantExp (I := I) (G := G) (t • X))) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hlog0 : (show E from mulInvariantLog (I := I) (G := G) (f 0)) = 0 := by
    rw [hf0]
    exact mulInvariantLog_one (I := I) (G := G)
  have hseq := tendsto_nsmul_apply_div_of_hasDerivAt hlog hlog0 t
  have hexp :=
    (contMDiff_mulInvariantExp (I := I) (G := G)).continuous.continuousAt.tendsto.comp hseq
  have hn : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => t / (n : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_comm, mul_zero] using hn.mul_const t
  have hfseq : Tendsto (fun n : ℕ => f (t / (n : ℝ))) atTop (nhds (1 : G)) := by
    have hf' := hf.tendsto
    rw [hf0] at hf'
    -- Expose the sequence as a composition so `ContinuousAt.tendsto` can consume `hs`.
    change Tendsto (f ∘ fun n : ℕ => t / (n : ℝ)) atTop (nhds (1 : G))
    exact hf'.comp hs
  have hevent := hfseq.eventually
    (eventually_mulInvariantExp_log (I := I) (G := G))
  apply hexp.congr'
  filter_upwards [hevent] with n hnlog
  -- Unwrap the tangent-space power formula before rewriting by the local exp-log inverse.
  change mulInvariantExp (I := I) (G := G)
      (n • (mulInvariantLog (I := I) (G := G) (f (t / (n : ℝ))) :
        GroupLieAlgebra I G)) = f (t / (n : ℝ)) ^ n
  rw [mulInvariantExp_nsmul, hnlog]

private theorem hasFDerivAt_mulInvariantLogChart_one [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    HasFDerivAt (mulInvariantLogChart (I := I) (G := G))
      (ContinuousLinearMap.id ℝ E) (extChartAt I (1 : G) (1 : G)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hexp : HasStrictFDerivAt (mulInvariantExpChart (I := I) (G := G))
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 :=
    (contDiffAt_mulInvariantExpChart_zero (I := I) (G := G)).hasStrictFDerivAt'
      (hasFDerivAt_mulInvariantExpChart_zero (I := I) (G := G)) (by simp)
  have hlog := hexp.to_local_left_inverse
    (eventually_mulInvariantLogChart_exp (I := I) (G := G))
  simpa using hlog.hasFDerivAt

-- Multiplication's tangent-map API and `extChartAt` use dependent tangent-space synonyms at
-- definitionally equal basepoints. The conversions below state each semantic boundary explicitly.
private theorem hasFDerivAt_mulInvariantExp_mul_chartCurve [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
    (X Y : GroupLieAlgebra I G) :
    HasFDerivAt
      (fun t : ℝ => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (t • X) *
          mulInvariantExp (I := I) (G := G) (t • Y)))
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((show E from X) + (show E from Y))) 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hX := hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G) X
  have hY := hasMFDerivAt_mulInvariantExp_smul_zero (I := I) (G := G) Y
  have hpair := hX.prodMk hY
  have hmul := (contMDiff_mul (G := G) I ∞).contMDiffAt
    (x := (mulInvariantExp (I := I) (G := G) ((0 : ℝ) • X),
      mulInvariantExp (I := I) (G := G) ((0 : ℝ) • Y)))
    |>.mdifferentiableAt (by simp)
  have hcurve := hmul.hasMFDerivAt.comp 0 hpair
  have hzero :
      mulInvariantExp (I := I) (G := G) ((0 : ℝ) • X) *
        mulInvariantExp (I := I) (G := G) ((0 : ℝ) • Y) = (1 : G) := by
    simp
  rw [hzero] at hcurve
  have hsource :
      mulInvariantExp (I := I) (G := G) ((0 : ℝ) • X) *
          mulInvariantExp (I := I) (G := G) ((0 : ℝ) • Y) ∈
        (chartAt H (1 : G)).source := by
    rw [hzero]
    exact mem_chart_source H (1 : G)
  have hext := (mdifferentiableAt_extChartAt (I := I)
    (x := (1 : G)) hsource).hasMFDerivAt
  have hchart := hext.comp 0 hcurve
  simp only [Function.comp_apply] at hchart
  rw [hzero] at hchart
  apply hchart.mdifferentiableAt.differentiableAt.hasFDerivAt.congr_fderiv
  rw [← mfderiv_eq_fderiv, hchart.mfderiv]
  apply DFunLike.coe_injective
  funext t
  let s : ℝ := show ℝ from t
  rw [show (0 : ℝ) • X = 0 by exact zero_smul ℝ X,
    show (0 : ℝ) • Y = 0 by exact zero_smul ℝ Y,
    mulInvariantExp_zero]
  have hmul_tangent := tangentMap_mul_prod_apply (I := I) (G := G)
    (⟨1, s • X⟩ : TangentBundle I G) (⟨1, s • Y⟩ : TangentBundle I G)
  have hmul_apply := congrArg (fun z : TangentBundle I G => z.2) hmul_tangent
  -- Project the bundled tangent-map equation to its fiberwise `mfderiv` statement.
  change
    (mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) ((1, 1) : G × G))
        (s • X, s • Y) =
      (mfderiv I I (fun z : G => z * 1) 1) (s • X) +
        (mfderiv I I (fun z : G => 1 * z) 1) (s • Y) at hmul_apply
  rw [show (fun z : G => z * 1) = id by funext z; simp,
    show (fun z : G => 1 * z) = id by funext z; simp, mfderiv_id] at hmul_apply
  -- Apply the two identity derivatives and expose scalar multiplication in the group tangent space.
  change
    (mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) ((1, 1) : G × G))
        (s • X, s • Y) = s • X + s • Y at hmul_apply
  have hmul_model := congrArg (fun Z : GroupLieAlgebra I G => show E from Z)
    (hmul_apply.trans (smul_add s X Y).symm)
  rw [mfderiv_extChartAt_self]
  -- `extChartAt` lands in the self-model, whose tangent space is the model-space synonym `E`.
  -- Expose that final chart boundary before applying the model-space equality above.
  change
    (show E from
      (mfderiv (I.prod I) I (fun p : G × G => p.1 * p.2) ((1, 1) : G × G))
        (s • X, s • Y)) =
      (show E from s • (X + Y))
  simpa only [s] using hmul_model

private theorem hasDerivAt_mulInvariantLog_mulInvariantExp_mul [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
    (X Y : GroupLieAlgebra I G) :
    HasDerivAt
      (fun t : ℝ => (show E from mulInvariantLog (I := I) (G := G)
        (mulInvariantExp (I := I) (G := G) (t • X) *
          mulInvariantExp (I := I) (G := G) (t • Y))))
      ((show E from X) + (show E from Y)) 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hlog := hasFDerivAt_mulInvariantLogChart_one (I := I) (G := G)
  have hcurve := hasFDerivAt_mulInvariantExp_mul_chartCurve (I := I) (G := G) X Y
  have hlog' : HasFDerivAt (mulInvariantLogChart (I := I) (G := G))
      (ContinuousLinearMap.id ℝ E)
      (extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) ((0 : ℝ) • X) *
          mulInvariantExp (I := I) (G := G) ((0 : ℝ) • Y))) := by
    simpa using hlog
  have hcomp' := (hlog'.comp 0 hcurve).hasDerivAt
  rw [show (mulInvariantLogChart (I := I) (G := G) ∘
      fun t : ℝ => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (t • X) *
          mulInvariantExp (I := I) (G := G) (t • Y))) =
      fun t : ℝ => (show E from mulInvariantLog (I := I) (G := G)
        (mulInvariantExp (I := I) (G := G) (t • X) *
          mulInvariantExp (I := I) (G := G) (t • Y))) by
    funext t
    exact (mulInvariantLog_eq_chart (I := I) (G := G) _).symm] at hcomp'
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using hcomp'

/-- The Trotter product formula for the tangent-space exponential. -/
theorem tendsto_mulInvariantExp_mul_pow_div [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
    (X Y : GroupLieAlgebra I G) (t : ℝ) :
    Tendsto (fun n : ℕ =>
      (mulInvariantExp (I := I) (G := G) ((t / n) • X) *
        mulInvariantExp (I := I) (G := G) ((t / n) • Y)) ^ n) atTop
      (nhds (mulInvariantExp (I := I) (G := G) (t • (X + Y)))) := by
  let f : ℝ → G := fun s =>
    mulInvariantExp (I := I) (G := G) (s • X) *
      mulInvariantExp (I := I) (G := G) (s • Y)
  have hf0 : f 0 = 1 := by simp [f]
  have hf : ContinuousAt f 0 := by
    exact ((contMDiff_mulInvariantExp_smul (I := I) (G := G) X).mul
      (contMDiff_mulInvariantExp_smul (I := I) (G := G) Y)).continuous.continuousAt
  have hlog := hasDerivAt_mulInvariantLog_mulInvariantExp_mul
    (I := I) (G := G) X Y
  simpa only [f] using
    tendsto_pow_div_of_hasDerivAt_mulInvariantLog (I := I) (G := G)
      (X + Y) hf0 hf hlog t

/-- The Trotter product formula for the exponential of left-invariant derivations. -/
theorem tendsto_lieExp_mul_pow_div [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
    (X Y : LeftInvariantDerivation I G) (t : ℝ) :
    Tendsto (fun n : ℕ => (lieExp ((t / n) • X) * lieExp ((t / n) • Y)) ^ n) atTop
      (nhds (lieExp (t • (X + Y)))) := by
  let L := leftInvariantDerivationEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  simpa only [lieExp_eq_mulInvariantExp, map_smul, map_add] using
    tendsto_mulInvariantExp_mul_pow_div (I := I) (G := G) (L X) (L Y) t
