/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
public import TauCeti.Analysis.Calculus.ContinuousMap

/-!
# Smooth parameter dependence for autonomous ODEs

This file develops the Banach-space implicit-equation argument that makes a local solution of a
smooth parameterized autonomous ODE depend smoothly on its parameter.

## Main results

* `ODE.exists_contDiffAt_picard_solution`: a finite-order smooth family of local solutions of the
  Picard integral equation, satisfying the ODE at interior times and from the right at the initial
  endpoint.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open scoped ContDiff

noncomputable section

universe u

namespace ODE

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Pair a parameter with every value of a continuous path, as a continuous linear map. -/
private noncomputable def parameterizedPath :
    E × C(K, F) →L[ℝ] C(K, E × F) := by
  let L : E × C(K, F) →ₗ[ℝ] C(K, E × F) :=
    { toFun := fun p ↦ ⟨fun t ↦ (p.1, p.2 t), continuous_const.prodMk p.2.continuous⟩
      map_add' := fun _ _ ↦ by ext t <;> rfl
      map_smul' := fun _ _ ↦ by ext t <;> rfl }
  exact LinearMap.mkContinuous L 1 fun p ↦ by
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg p)).2
    intro t
    rw [Prod.norm_def, Prod.norm_def]
    exact max_le_max le_rfl (ContinuousMap.norm_coe_le_norm p.2 t)

@[simp]
private theorem parameterizedPath_apply (p : E × C(K, F)) (t : K) :
    parameterizedPath p t = (p.1, p.2 t) := by
  rw [parameterizedPath]
  rfl

/-- The Picard integral equation, written as a zero of a map between Banach spaces of continuous
paths. -/
private noncomputable def picardResidual (f : C(E × F, F)) (x₀ : F) :
    E × C(Set.Icc (0 : ℝ) 1, F) → C(Set.Icc (0 : ℝ) 1, F) := fun p ↦
  p.2 - ContinuousMap.const _ x₀ -
    ContinuousMap.unitIntervalIntegral (f.comp (parameterizedPath p))

/-- The Picard residual is the path minus its initial value and integrated vector field. -/
@[simp]
private theorem picardResidual_apply (f : C(E × F, F)) (x₀ : F)
    (p : E × C(Set.Icc (0 : ℝ) 1, F)) :
    picardResidual f x₀ p = p.2 - ContinuousMap.const _ x₀ -
      ContinuousMap.unitIntervalIntegral (f.comp (parameterizedPath p)) := by
  rfl

/-- **A path's Picard residual vanishes exactly when it satisfies the Picard integral equation.**
The residual is the path minus the constant path at `x₀` minus the integrated field, so the two
sides are the same statement read as an equation of paths and pointwise on `[0, 1]` respectively.
Mathlib states the same equivalence for its own path space as `ODE.FunSpace.isFixedPt_next_iff`. -/
private theorem picardResidual_eq_zero_iff (gc : C(E × F, F)) (x₀ : F) (p : E)
    (q : C(Set.Icc (0 : ℝ) 1, F)) :
    picardResidual gc x₀ (p, q) = 0 ↔ ∀ t : Set.Icc (0 : ℝ) 1,
      q t = x₀ + ∫ s in (0 : ℝ)..t, gc (p, q (Set.projIcc 0 1 zero_le_one s)) := by
  simp [ContinuousMap.ext_iff, sub_sub, sub_eq_zero]

/-- A vector field of class `Cⁿ` gives a Picard residual of class `Cⁿ`. -/
private theorem contDiff_picardResidual (n : ℕ) (f : C(E × F, F))
    (hf : ContDiff ℝ n f) (x₀ : F) :
    ContDiff ℝ n (picardResidual f x₀) := by
  have hcomp : ContDiff ℝ n
      (fun p : E × C(Set.Icc (0 : ℝ) 1, F) ↦ f.comp (parameterizedPath p)) :=
    (ContinuousMap.contDiff_postcomp (n : ℕ∞) f (by simpa using hf)).comp
      (parameterizedPath (E := E) (F := F) (K := Set.Icc (0 : ℝ) 1)).contDiff
  exact (contDiff_snd.sub contDiff_const).sub
    ((ContinuousMap.unitIntervalIntegral (E := F)).contDiff.fun_comp hcomp)

/-- At a parameter for which the vector field vanishes locally in the state variable, the partial
derivative of the Picard residual in the path variable is the identity. -/
private theorem hasStrictFDerivAt_picardResidual_path
    (f : C(E × F, F)) (p₀ : E) (x₀ : F)
    (hf : ∀ᶠ y in nhds x₀, f (p₀, y) = 0) :
    HasStrictFDerivAt
      (fun γ : C(Set.Icc (0 : ℝ) 1, F) ↦ picardResidual f x₀ (p₀, γ))
      (ContinuousLinearMap.id ℝ C(Set.Icc (0 : ℝ) 1, F))
      (ContinuousMap.const _ x₀) := by
  have hzero : {y : F | f (p₀, y) = 0} ∈ nhds x₀ := hf
  obtain ⟨ε, hε, hεzero⟩ := Metric.mem_nhds_iff.mp hzero
  have heq :
      (fun γ : C(Set.Icc (0 : ℝ) 1, F) ↦
        γ - ContinuousMap.const _ x₀) =ᶠ[nhds (ContinuousMap.const _ x₀)]
      (fun γ ↦ picardResidual f x₀ (p₀, γ)) := by
    filter_upwards [Metric.ball_mem_nhds (ContinuousMap.const _ x₀) hε] with γ hγ
    have hcomp : f.comp (parameterizedPath (p₀, γ)) = 0 := by
      ext t
      apply hεzero
      rw [Metric.mem_ball]
      simpa only [parameterizedPath_apply, ContinuousMap.const_apply, Prod.snd] using
        (ContinuousMap.dist_apply_le_dist (f := γ)
          (g := ContinuousMap.const _ x₀) t).trans_lt hγ
    simp only [picardResidual_apply, hcomp, map_zero, sub_zero]
  exact (hasStrictFDerivAt_sub_const (ContinuousMap.const _ x₀)).congr_of_eventuallyEq heq

private theorem hasDerivWithinAt_Icc_of_forall_eq_picard
    [CompleteSpace F] (v : ℝ → F) (hv : Continuous v)
    (x₀ : F) (q : C(Set.Icc (0 : ℝ) 1, F))
    (hq : ∀ t : Set.Icc (0 : ℝ) 1,
      q t = x₀ + ∫ s in (0 : ℝ)..t, v s)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s ↦ q (Set.projIcc 0 1 zero_le_one s)) (v t)
      (Set.Icc 0 1) t := by
  let α : ℝ → F := fun s ↦ q (Set.projIcc 0 1 zero_le_one s)
  have hf : Continuous (Function.uncurry (fun s : ℝ ↦ fun _ : F ↦ v s)) :=
    hv.comp continuous_fst
  have hα : Continuous α := q.continuous.comp continuous_projIcc
  apply (ODE.hasDerivWithinAt_picard_Icc (E := F) (f := fun s _ ↦ v s) (α := α)
    (u := Set.univ) (t₀ := 0) (tmin := 0) (tmax := 1) ⟨le_rfl, zero_le_one⟩
    hf.continuousOn hα.continuousOn (fun _ _ ↦ Set.mem_univ _) x₀ ht).congr_of_mem
  · intro s hs
    simp only [ODE.picard_apply, α, Set.projIcc_of_mem zero_le_one hs]
    exact hq ⟨s, hs⟩
  · exact ht

/-- **The path-derivative of the Picard residual at the constant base solution is invertible.**
For a continuously differentiable field vanishing near `x₀` at the base parameter `p₀`, the
restriction of
`fderiv ℝ (picardResidual gc x₀)` to the path direction is invertible at `(p₀, const x₀)`. -/
private theorem isInvertible_fderiv_picardResidual_comp_inr
    (gc : C(E × F, F)) (hg : ContDiff ℝ 1 gc) (p₀ : E) (x₀ : F)
    (hgzero : ∀ᶠ y in nhds x₀, gc (p₀, y) = 0) :
    (fderiv ℝ (picardResidual gc x₀)
          (p₀, (ContinuousMap.const _ x₀ : C(Set.Icc (0 : ℝ) 1, F))) ∘L
        ContinuousLinearMap.inr ℝ E C(Set.Icc (0 : ℝ) 1, F)).IsInvertible := by
  have hR : ContDiffAt ℝ 1 (picardResidual gc x₀)
      (p₀, (ContinuousMap.const _ x₀ : C(Set.Icc (0 : ℝ) 1, F))) :=
    (contDiff_picardResidual 1 gc hg x₀).contDiffAt
  have hpartial := hasStrictFDerivAt_picardResidual_path gc p₀ x₀ hgzero
  have hdiff := hR.differentiableAt (by norm_num)
  have hpartialEq :=
    (hdiff.hasFDerivAt.comp (ContinuousMap.const (Set.Icc (0 : ℝ) 1) x₀)
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) p₀
        (ContinuousMap.const (Set.Icc (0 : ℝ) 1) x₀))).unique hpartial.hasFDerivAt
  rw [hpartialEq]
  exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩

/-- **A parameter-to-path germ continuous at the base parameter keeps its whole path near the
base point.** If `γ` is continuous at `p₀` and `γ p₀` is the constant path at `x₀`, then for `p`
near `p₀` the parameterized path `(p, γ p)` stays within any prescribed distance of the constant
path at `(p₀, x₀)`. -/
private theorem eventually_dist_parameterizedPath_lt {γ : E → C(K, F)} {p₀ : E}
    {x₀ : F} (hγcont : ContinuousAt γ p₀)
    (hγbase : γ p₀ = ContinuousMap.const _ x₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in nhds p₀,
      dist (parameterizedPath (p, γ p)) (ContinuousMap.const K (p₀, x₀)) < ε := by
  have hpath := parameterizedPath.continuous.continuousAt.comp
    (continuousAt_id.prodMk hγcont)
  have hpathBase : parameterizedPath (p₀, γ p₀) =
      ContinuousMap.const _ (p₀, x₀) := by
    rw [hγbase]
    apply ContinuousMap.ext
    intro t
    rw [parameterizedPath_apply, ContinuousMap.const_apply]
    rw [ContinuousMap.const_apply]
  simpa only [hpathBase, Function.comp_apply, id_eq] using
    (Metric.continuousAt_iff'.mp hpath ε hε)

/-- A smooth parameterized autonomous vector field which vanishes at the base parameter admits a
locally smooth family of solutions through a fixed initial state. The result is stated at every
finite order; this is the form needed to assemble smoothness of a germ. Each nearby path satisfies
the Picard integral equation, the corresponding ODE at every interior time, and its right-hand
version at the initial endpoint. -/
theorem exists_contDiffAt_picard_solution
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (n : ℕ) (f : E × F → F) (p₀ : E) (x₀ : F)
    (hf : ContDiffAt ℝ (n + 1) f (p₀, x₀))
    (hzero : ∀ᶠ y in nhds x₀, f (p₀, y) = 0) :
    ∃ γ : E → C(Set.Icc (0 : ℝ) 1, F),
      ContDiffAt ℝ (n + 1) γ p₀ ∧
      γ p₀ = ContinuousMap.const _ x₀ ∧
      ∀ᶠ p in nhds p₀,
        (∀ t : Set.Icc (0 : ℝ) 1,
          γ p t = x₀ + ∫ s in (0 : ℝ)..t,
            f (p, γ p (Set.projIcc 0 1 zero_le_one s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt (fun s ↦ γ p (Set.projIcc 0 1 zero_le_one s))
            (f (p, γ p (Set.projIcc 0 1 zero_le_one t))) t) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) 1,
          HasDerivWithinAt (fun s ↦ γ p (Set.projIcc 0 1 zero_le_one s))
            (f (p, γ p (Set.projIcc 0 1 zero_le_one t))) (Set.Ici t) t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  -- Replace the local vector-field germ by a global smooth representative so the Banach-space
  -- implicit function theorem applies without changing the ODE near the base point.
  obtain ⟨g, hg, hgf⟩ :=
    hf.exists_contDiff_eventuallyEq_of_finiteDimensional (n + 1)
  let gc : C(E × F, F) := ⟨g, hg.continuous⟩
  let R := picardResidual gc x₀
  let basePath : C(Set.Icc (0 : ℝ) 1, F) := ContinuousMap.const _ x₀
  let u : E × C(Set.Icc (0 : ℝ) 1, F) := (p₀, basePath)
  have hR : ContDiffAt ℝ (n + 1) R u :=
    (contDiff_picardResidual (n + 1) gc hg x₀).contDiffAt
  have hgfBase : g (p₀, x₀) = f (p₀, x₀) :=
    hgf.self_of_nhds
  have hzeroBase : f (p₀, x₀) = 0 := hzero.self_of_nhds
  have hgzero : ∀ᶠ y in nhds x₀, gc (p₀, y) = 0 := by
    have hpull : ∀ᶠ y in nhds x₀, g (p₀, y) = f (p₀, y) :=
      (continuousAt_const.prodMk continuousAt_id).eventually hgf
    filter_upwards [hpull, hzero] with y hy hyzero
    exact hy.trans hyzero
  -- At the constant base solution the path derivative of the residual is the identity, so the
  -- implicit function theorem produces a smooth parameter-to-path germ.
  have hinvertible :
      (fderiv ℝ R u ∘L
        ContinuousLinearMap.inr ℝ E C(Set.Icc (0 : ℝ) 1, F)).IsInvertible :=
    isInvertible_fderiv_picardResidual_comp_inr gc (hg.of_le (by norm_num)) p₀ x₀ hgzero
  let γ : E → C(Set.Icc (0 : ℝ) 1, F) :=
    hR.implicitFunction (by norm_num) hinvertible
  have hγsmooth : ContDiffAt ℝ (n + 1) γ p₀ :=
    hR.contDiffAt_implicitFunction (by norm_num) hinvertible
  have hγbase : γ p₀ = basePath :=
    hR.implicitFunction_apply_self (by norm_num) hinvertible
  have hRbase : R u = 0 := by
    have hcomp : gc.comp (parameterizedPath u) = 0 := by
      ext t
      rw [ContinuousMap.comp_apply, parameterizedPath_apply]
      simp only [gc, u, basePath, ContinuousMap.const_apply]
      exact hgfBase.trans hzeroBase
    simp only [R, picardResidual_apply, u, basePath, hcomp, map_zero, sub_self]
  have hγeq : ∀ᶠ p in nhds p₀, R (p, γ p) = 0 := by
    filter_upwards [hR.eventually_apply_implicitFunction (by norm_num) hinvertible] with p hp
    rw [hp, hRbase]
  have hgfSet : {z : E × F | g z = f z} ∈ nhds (p₀, x₀) := hgf
  obtain ⟨ε, hε, hεgf⟩ := Metric.mem_nhds_iff.mp hgfSet
  have hpathsNear := eventually_dist_parameterizedPath_lt (γ := γ)
    hγsmooth.continuousAt (by simpa only [basePath] using hγbase) hε
  -- Restrict to parameters whose whole Picard path remains where the cutoff field agrees with
  -- the original field; then transfer the integral equation and its derivative consequences.
  refine ⟨γ, hγsmooth, by simpa only [basePath] using hγbase, ?_⟩
  filter_upwards [hγeq, hpathsNear] with p hp hpnear
  have hpoint (t : Set.Icc (0 : ℝ) 1) :
      gc (parameterizedPath (p, γ p) t) = f (p, γ p t) := by
    apply hεgf
    rw [Metric.mem_ball]
    simpa only [parameterizedPath_apply, ContinuousMap.const_apply] using
      (ContinuousMap.dist_apply_le_dist
        (f := parameterizedPath (p, γ p))
        (g := ContinuousMap.const _ (p₀, x₀)) t).trans_lt hpnear
  have hpicard : ∀ t : Set.Icc (0 : ℝ) 1,
      γ p t = x₀ + ∫ s in (0 : ℝ)..t,
        gc (p, γ p (Set.projIcc 0 1 zero_le_one s)) :=
    (picardResidual_eq_zero_iff gc x₀ p (γ p)).mp hp
  let vproj : ℝ → F := fun s ↦ gc (p, γ p (Set.projIcc 0 1 zero_le_one s))
  have hvproj : Continuous vproj :=
    gc.continuous.comp
      (continuous_const.prodMk ((γ p).continuous.comp continuous_projIcc))
  refine ⟨fun t ↦ (hpicard t).trans (congrArg (x₀ + ·) ?_), ?_, ?_⟩
  · apply intervalIntegral.integral_congr
    intro s _
    exact hpoint (Set.projIcc 0 1 zero_le_one s)
  · intro t ht
    have hderiv :=
      (hasDerivWithinAt_Icc_of_forall_eq_picard vproj hvproj x₀ (γ p) hpicard
        ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    exact hderiv.congr_deriv (hpoint (Set.projIcc 0 1 zero_le_one t))
  · intro t ht
    have hIcc := hasDerivWithinAt_Icc_of_forall_eq_picard vproj hvproj x₀ (γ p) hpicard
      ⟨ht.1, ht.2.le⟩
    have hsmall := hIcc.mono (Set.Icc_subset_Icc ht.1 le_rfl)
    have hderiv : HasDerivWithinAt
        (fun s ↦ γ p (Set.projIcc 0 1 zero_le_one s)) (vproj t) (Set.Ici t) t := by
      apply hsmall.congr_set
      filter_upwards [Iic_mem_nhds ht.2] with s hs
      apply propext
      constructor
      · exact fun h ↦ h.1
      · exact fun h ↦ ⟨h, hs⟩
    exact hderiv.congr_deriv (hpoint (Set.projIcc 0 1 zero_le_one t))

end ODE
