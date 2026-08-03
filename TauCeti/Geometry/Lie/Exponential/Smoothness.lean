/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.ODE.SmoothParameter
public import TauCeti.Geometry.Lie.Exponential.ParameterDependence

/-!
# Smoothness of the Lie-group exponential

This file upgrades the continuous local invariant flow to smooth parameter dependence and uses it
to prove that the Lie-group exponential is smooth at the zero vector.

## Main results

* `contMDiffAt_mulInvariantExp_zero`: the tangent-space exponential is smooth at zero.
* `contMDiff_mulInvariantExp`: the tangent-space exponential is smooth everywhere.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open Bundle Function Manifold VectorField
open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G] [IsManifold I 2 G]

local instance lieGroupMinSmoothnessSmoothness [LieGroup I ∞ G] :
    LieGroup I (minSmoothness ℝ 3) G := by
  simpa using (inferInstance : LieGroup I (3 : ℕ∞ω) G)

omit [IsManifold I 2 G] in
/-- The tangent-space exponential of a finite-dimensional smooth Lie group is smooth at zero. -/
theorem contMDiffAt_mulInvariantExp_zero
    [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    ContMDiffAt 𝓘(ℝ, E) I ∞
      (fun v : E => mulInvariantExp (I := I) (G := G)
        (v : GroupLieAlgebra I G)) 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ContMDiffMul I (∞ + 1) G := by
    simpa using (inferInstance : ContMDiffMul I ∞ G)
  let center : E := extChartAt I (1 : G) (1 : G)
  obtain ⟨α, U, δ, hU, hδ, hαlocal, hαeq⟩ :=
    exists_local_coordinate_representation_mulInvariantIntegralCurve (I := I) (G := G)
  let c : ℝ := δ / 2
  have hc : 0 < c := by dsimp only [c]; linarith
  have hcδ : c < δ := by dsimp only [c]; linarith
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hzeroU : (0 : E) ∈ U := mem_of_mem_nhds hU
  rw [contMDiffAt_infty]
  intro n
  have hcoord : ContDiffAt ℝ n
      (fun v : E => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G))) 0 := by
    let F : E × E → E := fun p => c •
      mulInvariantCoordinateVectorField (I := I) (G := G) p
    have hF : ContDiffAt ℝ (n + 1) F ((0 : E), center) := by
      exact contDiffAt_const.smul
        ((contDiffAt_mulInvariantCoordinateVectorField (I := I) (G := G) (v := 0) (n := ∞)
          BoundarylessManifold.isInteriorPoint).of_le
          (by exact_mod_cast le_top))
    have hFzero : ∀ᶠ y in 𝓝 center, F (0, y) = 0 := by
      filter_upwards [] with y
      simp only [F, mulInvariantCoordinateVectorField_zero, smul_zero]
    obtain ⟨γ, hγsmooth, hγzero, hγode⟩ :=
      ODE.exists_contDiffAt_picard_solution n F (0 : E) center hF hFzero
    have hFone : ContDiffAt ℝ 1 F ((0 : E), center) :=
      hF.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    obtain ⟨K, W, hW, hFlip⟩ := hFone.exists_lipschitzOnWith
    rw [nhds_prod_eq] at hW
    obtain ⟨P, hP, S, hS, hPS⟩ := Filter.mem_prod_iff.mp hW
    have hfixed (p : E) (hp : p ∈ P) : LipschitzOnWith K (fun y => F (p, y)) S := by
      intro y hy z hz
      have h := hFlip (x := (p, y)) (y := (p, z))
        (hPS ⟨hp, hy⟩) (hPS ⟨hp, hz⟩)
      simpa only [Prod.edist_eq, edist_self, zero_max] using h
    obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.mp hS
    have hγS : ∀ᶠ p in 𝓝 (0 : E), ∀ t : Set.Icc (0 : ℝ) 1, γ p t ∈ S := by
      have hnear := hγsmooth.continuousAt
        (show Metric.ball (ContinuousMap.const _ center) ε ∈ 𝓝 (γ 0) by
          rw [hγzero]
          exact Metric.ball_mem_nhds _ hε)
      filter_upwards [hnear] with p hp
      intro t
      apply hεS
      rw [Metric.mem_ball]
      simpa only [hγzero, ContinuousMap.const_apply] using
        (ContinuousMap.dist_apply_le_dist (f := γ p)
          (g := ContinuousMap.const _ center) t).trans_lt hp
    have hexpCoord : ContinuousAt
        (fun v : E => extChartAt I (1 : G)
          (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G))) 0 := by
      have hexp : ContinuousAt
          (fun v : E => mulInvariantExp (I := I) (G := G)
            (v : GroupLieAlgebra I G)) 0 :=
        continuousAt_mulInvariantExp_modelSpace_zero (I := I) (G := G)
      have hzero : mulInvariantExp (I := I) (G := G)
          (0 : GroupLieAlgebra I G) = 1 := mulInvariantExp_zero
      exact (continuousAt_extChartAt (I := I) (1 : G)).comp_of_eq hexp hzero
    have hcoordS : (fun v : E => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (v : GroupLieAlgebra I G))) ⁻¹' S ∈ 𝓝 (0 : E) :=
      by
        have hzero : mulInvariantExp (I := I) (G := G)
            (0 : GroupLieAlgebra I G) = 1 := mulInvariantExp_zero
        apply hexpCoord.preimage_mem_nhds
        change S ∈ 𝓝 (extChartAt I (1 : G)
          (mulInvariantExp (I := I) (G := G) (0 : GroupLieAlgebra I G)))
        rw [hzero]
        exact hS
    obtain ⟨η, hη, hηS⟩ := Metric.mem_nhds_iff.mp hcoordS
    have hradius : 0 < η / (c + 1) := div_pos hη (by linarith)
    have hcanonicalS : ∀ᶠ p : E in 𝓝 (0 : E), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        extChartAt I (1 : G)
          (mulInvariantExp (I := I) (G := G)
            ((c * t) • (p : GroupLieAlgebra I G))) ∈ S := by
      filter_upwards [Metric.ball_mem_nhds (0 : E) hradius] with p hp
      intro t ht
      apply hηS
      rw [Metric.mem_ball, dist_zero_right] at hp ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le ht.1)]
      have hct : c * t ≤ c := mul_le_of_le_one_right hc.le ht.2
      have hmul : c * ‖p‖ < c * (η / (c + 1)) :=
        mul_lt_mul_of_pos_left hp hc
      calc
        c * t * ‖p‖ ≤ c * ‖p‖ := mul_le_mul_of_nonneg_right hct (norm_nonneg p)
        _ < c * (η / (c + 1)) := hmul
        _ < η := by
          have hcfrac : c / (c + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
          calc
            c * (η / (c + 1)) = (c / (c + 1)) * η := by ring
            _ < 1 * η := mul_lt_mul_of_pos_right hcfrac hη
            _ = η := one_mul η
    have hEq : ∀ᶠ p in 𝓝 (0 : E),
        γ p ⟨1, zero_le_one, le_rfl⟩ =
          extChartAt I (1 : G)
            (mulInvariantExp (I := I) (G := G)
              (c • (p : GroupLieAlgebra I G))) := by
      filter_upwards [hγode, hγS, hcanonicalS, hP, hU] with p hpODE hpγS hpCanonicalS hpP hpU
      let g : ℝ → E := fun t => γ p (Set.projIcc 0 1 zero_le_one t)
      let a : ℝ → E := fun t =>
        (α (((p, center), c * t))).2
      have htime (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
          c * t ∈ Set.Ioo (-δ) δ := by
        constructor
        · nlinarith [mul_nonneg hc.le ht.1]
        · exact (mul_le_of_le_one_right hc.le ht.2).trans_lt hcδ
      have haCoord (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
          a t = extChartAt I (1 : G)
            (mulInvariantExp (I := I) (G := G)
              ((c * t) • (p : GroupLieAlgebra I G))) := by
        have hlocal := hαlocal p hpU (c * t) (htime t ht)
        have htarget := hlocal.2.2.2.2
        have htarget' : a t ∈ (extChartAt I (1 : G)).target := by
          exact interior_subset (by simpa only [a, center] using htarget)
        calc
          a t = extChartAt I (1 : G) ((extChartAt I (1 : G)).symm (a t)) :=
            ((extChartAt I (1 : G)).right_inv htarget').symm
          _ = extChartAt I (1 : G)
              (mulInvariantIntegralCurve (I := I) (G := G)
                (p : GroupLieAlgebra I G) 1 (c * t)) := by
            congr 1
            exact hαeq p hpU (htime t ht)
          _ = extChartAt I (1 : G)
              (mulInvariantExp (I := I) (G := G)
                ((c * t) • (p : GroupLieAlgebra I G))) := by
            exact congrArg (extChartAt I (1 : G))
              (mulInvariantExp_smul (I := I) (G := G)
                (p : GroupLieAlgebra I G) (c * t)).symm
      have haCont : ContinuousOn a (Set.Icc (0 : ℝ) 1) := by
        intro t ht
        have hlocal := hαlocal p hpU (c * t) (htime t ht)
        have hinner : ContinuousAt
            (fun s : ℝ => ((p, extChartAt I (1 : G) (1 : G)), c * s)) t := by fun_prop
        have hαcomp : ContinuousAt
            (fun s : ℝ => α ((p, extChartAt I (1 : G) (1 : G)), c * s)) t :=
          hlocal.1.comp_of_eq hinner rfl
        simpa only [a, center] using (continuousAt_snd.comp' hαcomp).continuousWithinAt
      have haDeriv : ∀ t ∈ Set.Ico (0 : ℝ) 1,
          HasDerivWithinAt a (F (p, a t)) (Set.Ici t) t := by
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
        have hlocal := hαlocal p hpU (c * t) (htime t ht')
        have hcomp : HasDerivAt
            (fun s : ℝ => α ((p, extChartAt I (1 : G) (1 : G)), c * s))
            (c • ((0 : E), mulInvariantCoordinateVectorField (I := I) (G := G)
              (α ((p, extChartAt I (1 : G) (1 : G)), c * t)))) t :=
          HasDerivAt.scomp t hlocal.2.1 (hasDerivAt_const_mul c)
        have hsnd := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t hcomp
        apply hsnd.hasDerivWithinAt.congr_deriv
        have hpair : α (((p, center), c * t)) = (p, a t) := by
          apply Prod.ext
          · exact hlocal.2.2.2.1
          · rfl
        have hpair' : α (((p, extChartAt I (1 : G) (1 : G)), c * t)) = (p, a t) := by
          simpa only [center] using hpair
        simp only [F, map_smul]
        rw [hpair']
        rfl
      have hgCont : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
        ((γ p).continuous.comp continuous_projIcc).continuousOn
      have hgDeriv : ∀ t ∈ Set.Ico (0 : ℝ) 1,
          HasDerivWithinAt g (F (p, g t)) (Set.Ici t) t := hpODE.2.2
      have haS : ∀ t ∈ Set.Ico (0 : ℝ) 1, a t ∈ S := by
        intro t ht
        rw [haCoord t ⟨ht.1, ht.2.le⟩]
        exact hpCanonicalS t ⟨ht.1, ht.2.le⟩
      have hgS : ∀ t ∈ Set.Ico (0 : ℝ) 1, g t ∈ S := by
        intro t ht
        exact hpγS (Set.projIcc 0 1 zero_le_one t)
      have hga0 : g 0 = a 0 := by
        have hg0 := hpODE.1 ⟨0, le_rfl, zero_le_one⟩
        have ha0 := (hαlocal p hpU 0 (by simpa using htime 0 ⟨le_rfl, zero_le_one⟩)).2.2.1
        have hg0' : g 0 = center := by
          change γ p (Set.projIcc 0 1 zero_le_one 0) = center
          rw [show Set.projIcc 0 1 zero_le_one 0 =
            (⟨0, le_rfl, zero_le_one⟩ : Set.Icc (0 : ℝ) 1) by ext; simp]
          simpa using hg0
        have ha0' : a 0 = center := by
          change (α (((p, center), c * 0))).2 = center
          rw [mul_zero]
          simpa only [center] using congrArg Prod.snd ha0
        exact hg0'.trans ha0'.symm
      have hunique := ODE_solution_unique_of_mem_Icc_right
        (v := fun _ y => F (p, y)) (s := fun _ => S)
        (fun _ _ => hfixed p hpP) hgCont hgDeriv hgS haCont haDeriv haS hga0
      have hone := hunique (show (1 : ℝ) ∈ Set.Icc 0 1 by exact ⟨zero_le_one, le_rfl⟩)
      have hone' := hone.trans (haCoord 1 ⟨zero_le_one, le_rfl⟩)
      change γ p ⟨1, zero_le_one, le_rfl⟩ = _
      rw [← show Set.projIcc 0 1 zero_le_one 1 =
        (⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1) by ext; simp]
      simpa only [g, mul_one] using hone'
    have heval : ContDiffAt ℝ (n + 1)
        (fun p => γ p ⟨1, zero_le_one, le_rfl⟩) 0 :=
      by
        simpa only [Function.comp_def, ContinuousMap.evalCLM_apply] using
          hγsmooth.continuousLinearMap_comp
            (ContinuousMap.evalCLM ℝ ⟨1, zero_le_one, le_rfl⟩)
    have hscaled : ContDiffAt ℝ (n + 1)
        (fun p : E => extChartAt I (1 : G)
          (mulInvariantExp (I := I) (G := G)
            (c • (p : GroupLieAlgebra I G)))) 0 :=
      by
        apply heval.congr_of_eventuallyEq
        filter_upwards [hEq] with p hp
        exact hp.symm
    have hrescale : ContDiffAt ℝ (n + 1) (fun p : E => c⁻¹ • p) 0 := by fun_prop
    have hscaled' : ContDiffAt ℝ (n + 1)
        (fun p : E => extChartAt I (1 : G)
          (mulInvariantExp (I := I) (G := G)
            (c • (p : GroupLieAlgebra I G)))) (c⁻¹ • (0 : E)) := by
      simpa only [smul_zero] using hscaled
    have hcomp := hscaled'.comp 0 hrescale
    apply (hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)).of_le
      (by exact_mod_cast Nat.le_succ n)
    have harg : c • ((c⁻¹ • p : E) : GroupLieAlgebra I G) =
        (p : GroupLieAlgebra I G) := by
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    change extChartAt I (1 : G)
      (mulInvariantExp (I := I) (G := G) (p : GroupLieAlgebra I G)) =
        extChartAt I (1 : G)
          (mulInvariantExp (I := I) (G := G)
            (c • ((c⁻¹ • p : E) : GroupLieAlgebra I G)))
    rw [harg]
  have hzero : mulInvariantExp (I := I) (G := G)
      (0 : GroupLieAlgebra I G) = 1 := mulInvariantExp_zero
  rw [contMDiffAt_iff_target_of_mem_source (y := (1 : G)) (by
    convert mem_chart_source H (1 : G) using 1
    exact hzero)]
  refine ⟨continuousAt_mulInvariantExp_modelSpace_zero (I := I) (G := G), ?_⟩
  have hcoordM := hcoord.contMDiffAt
  simpa only [Function.comp_def] using hcoordM

omit [IsManifold I 2 G] in
private theorem mulInvariantExp_nsmul
    [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
    (v : GroupLieAlgebra I G) (m : ℕ) :
    mulInvariantExp (I := I) (G := G) (m • v) =
      mulInvariantExp (I := I) (G := G) v ^ m := by
  have h := map_pow (mulInvariantOneParameterSubgroup (I := I) (G := G) v)
    (Multiplicative.ofAdd (1 : ℝ)) m
  rw [← ofAdd_nsmul] at h
  simpa only [nsmul_eq_mul, mul_one, Nat.cast_smul_eq_nsmul,
    mulInvariantOneParameterSubgroup_eq_mulInvariantExp_smul, one_smul] using h

omit [IsManifold I 2 G] in
/-- The tangent-space exponential of a finite-dimensional smooth Lie group is smooth. Smoothness
at zero globalizes because every vector can be divided by a sufficiently large positive integer,
and `exp v = (exp (v / m)) ^ m`. -/
theorem contMDiff_mulInvariantExp
    [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G] :
    ContMDiff 𝓘(ℝ, E) I ∞
      (fun v : E => mulInvariantExp (I := I) (G := G)
        (v : GroupLieAlgebra I G)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [contMDiff_infty]
  intro n x
  have hzero : ContMDiffAt 𝓘(ℝ, E) I n
      (fun v : E => mulInvariantExp (I := I) (G := G)
        (v : GroupLieAlgebra I G)) 0 :=
    contMDiffAt_mulInvariantExp_zero (I := I) (G := G) |>.of_le
      (by exact_mod_cast le_top)
  have hnear : ∀ᶠ y in 𝓝 (0 : E),
      ContMDiffAt 𝓘(ℝ, E) I n
        (fun v : E => mulInvariantExp (I := I) (G := G)
          (v : GroupLieAlgebra I G)) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hzero)
  obtain ⟨ε, hε, hεnear⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨m, hm⟩ := exists_nat_gt (‖x‖ / ε)
  have hmpos : 0 < (m : ℝ) :=
    (div_nonneg (norm_nonneg x) hε.le).trans_lt hm
  have hm0 : m ≠ 0 := by exact_mod_cast hmpos.ne'
  have hxsmall : (m : ℝ)⁻¹ • x ∈ Metric.ball (0 : E) ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hmpos]
    apply (inv_mul_lt_iff₀ hmpos).2
    exact (div_lt_iff₀ hε).mp hm
  have hsmall := hεnear hxsmall
  have hscale : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n
      (fun y : E => (m : ℝ)⁻¹ • y) x :=
    (contDiff_const_smul (𝕜 := ℝ) (F := E) (m : ℝ)⁻¹).contDiffAt.contMDiffAt
  have hscaled : ContMDiffAt 𝓘(ℝ, E) I n
      (fun y : E => mulInvariantExp (I := I) (G := G)
        (((m : ℝ)⁻¹ • y : E) : GroupLieAlgebra I G)) x := by
    simpa only [Function.comp_def] using hsmall.comp x hscale
  have hpow : ContMDiffAt 𝓘(ℝ, E) I n
      (fun y : E => mulInvariantExp (I := I) (G := G)
        (((m : ℝ)⁻¹ • y : E) : GroupLieAlgebra I G) ^ m) x := by
    simpa only [Function.comp_def] using
      (contMDiff_pow m).contMDiffAt.comp x hscaled
  apply hpow.congr_of_eventuallyEq
  filter_upwards [] with y
  symm
  calc
    mulInvariantExp (I := I) (G := G)
          (((m : ℝ)⁻¹ • y : E) : GroupLieAlgebra I G) ^ m =
        mulInvariantExp (I := I) (G := G)
          (m • (((m : ℝ)⁻¹ • y : E) : GroupLieAlgebra I G)) :=
      (mulInvariantExp_nsmul (I := I) (G := G)
        (((m : ℝ)⁻¹ • y : E) : GroupLieAlgebra I G) m).symm
    _ = mulInvariantExp (I := I) (G := G) (y : GroupLieAlgebra I G) := by
      congr 1
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hm0), one_smul]
