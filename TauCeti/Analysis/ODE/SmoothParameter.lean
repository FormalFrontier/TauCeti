/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.Calculus.ContinuousMap

/-!
# Smooth parameter dependence for autonomous ODEs

This file develops the Banach-space implicit-equation argument that makes a local solution of a
smooth parameterized autonomous ODE depend smoothly on its parameter.

## Main results

* `ODE.exists_contDiffAt_picard_solution`: a finite-order smooth family of local solutions of the
  Picard integral equation.
* `ODE.hasDerivAt_of_forall_eq_picard`: a Picard solution satisfies the ODE at interior times.
* `ODE.hasDerivWithinAt_Ici_of_forall_eq_picard`: a Picard solution has the required right
  derivative at its initial endpoint.

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

/-- A finite-order smooth germ on a finite-dimensional real normed space has a globally smooth
representative of the same order. A smooth bump cuts the function off inside a neighborhood on
which the original germ is smooth. -/
theorem exists_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] (n : ℕ) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ g =ᶠ[nhds x] f := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  let b : ContDiffBump x :=
    ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let g : E → F := fun y ↦ b y • f y
  have hball : ContDiffOn ℝ n f (Metric.ball x ε) :=
    hfs.mono hεs
  have hg : ContDiff ℝ n g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport b
    · have hyClosed : y ∈ Metric.closedBall x (ε / 2) := by
        simpa only [b, ContDiffBump.tsupport_eq] using hy
      have hyBall : y ∈ Metric.ball x ε := by
        rw [Metric.mem_ball]
        exact hyClosed.trans_lt (by linarith)
      exact b.contDiffAt.smul
        ((hball y hyBall).contDiffAt (Metric.isOpen_ball.mem_nhds hyBall))
    · have hbzero : (b : E → ℝ) =ᶠ[nhds y] fun _ ↦ 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hy
      have hgeq : g =ᶠ[nhds y] fun _ ↦ (0 : F) := by
        filter_upwards [hbzero] with z hz
        simp only [g, hz, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hgeq
  refine ⟨g, hg, ?_⟩
  filter_upwards [b.eventuallyEq_one] with y hy
  change b y = 1 at hy
  simp only [g, hy, one_smul]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Pair a parameter with every value of a continuous path, as a continuous linear map. -/
noncomputable def parameterizedPath :
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
theorem parameterizedPath_apply (p : E × C(K, F)) (t : K) :
    parameterizedPath p t = (p.1, p.2 t) := by
  rw [parameterizedPath]
  rfl

/-- The Picard integral equation, written as a zero of a map between Banach spaces of continuous
paths. -/
noncomputable def picardResidual (f : C(E × F, F)) (x₀ : F) :
    E × C(Set.Icc (0 : ℝ) 1, F) → C(Set.Icc (0 : ℝ) 1, F) := fun p ↦
  p.2 - ContinuousMap.const _ x₀ -
    ContinuousMap.unitIntervalIntegral (f.comp (parameterizedPath p))

/-- A smooth vector field gives a smooth Picard residual. -/
theorem contDiff_picardResidual (n : ℕ) (f : C(E × F, F))
    (hf : ContDiff ℝ n f) (x₀ : F) :
    ContDiff ℝ n (picardResidual f x₀) := by
  have hcomp : ContDiff ℝ n
      (fun p : E × C(Set.Icc (0 : ℝ) 1, F) ↦ f.comp (parameterizedPath p)) :=
    (ContinuousMap.contDiff_comp_nat n f hf).comp
      (parameterizedPath (E := E) (F := F) (K := Set.Icc (0 : ℝ) 1)).contDiff
  exact (contDiff_snd.sub contDiff_const).sub
    ((ContinuousMap.unitIntervalIntegral (E := F)).contDiff.fun_comp hcomp)

/-- At a parameter for which the vector field vanishes locally in the state variable, the partial
derivative of the Picard residual in the path variable is the identity. -/
theorem hasStrictFDerivAt_picardResidual_parameter
    [CompleteSpace F] (f : C(E × F, F)) (p₀ : E) (x₀ : F)
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
    simp only [picardResidual, hcomp, map_zero, sub_zero]
  exact (hasStrictFDerivAt_sub_const (ContinuousMap.const _ x₀)).congr_of_eventuallyEq heq

/-- A path satisfying the Picard integral equation solves the corresponding ODE at every interior
time. Projection to the unit interval makes the path a total function on `ℝ`. -/
theorem hasDerivAt_of_forall_eq_picard
    [CompleteSpace F] (v : ℝ → F) (hv : Continuous v)
    (x₀ : F) (q : C(Set.Icc (0 : ℝ) 1, F))
    (hq : ∀ t : Set.Icc (0 : ℝ) 1,
      q t = x₀ + ∫ s in (0 : ℝ)..t, v s)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ q (Set.projIcc 0 1 zero_le_one s)) (v t) t := by
  have hprimitive : HasDerivAt (fun s ↦ x₀ + ∫ u in (0 : ℝ)..s, v u) (v t) t := by
    have h := (hasDerivAt_const (𝕜 := ℝ) t x₀).add
      (hv.integral_hasStrictDerivAt 0 t).hasDerivAt
    convert h using 1
    · funext s
      rfl
    · simp
  apply hprimitive.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  rw [Set.projIcc_of_mem zero_le_one ⟨hs.1.le, hs.2.le⟩]
  exact hq ⟨s, hs.1.le, hs.2.le⟩

/-- A path satisfying the Picard integral equation has the corresponding right derivative at the
initial endpoint as well as at every time before the terminal endpoint. -/
theorem hasDerivWithinAt_Ici_of_forall_eq_picard
    [CompleteSpace F] (v : ℝ → F) (hv : Continuous v)
    (x₀ : F) (q : C(Set.Icc (0 : ℝ) 1, F))
    (hq : ∀ t : Set.Icc (0 : ℝ) 1,
      q t = x₀ + ∫ s in (0 : ℝ)..t, v s)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    HasDerivWithinAt (fun s ↦ q (Set.projIcc 0 1 zero_le_one s)) (v t)
      (Set.Ici t) t := by
  have hprimitive : HasDerivAt (fun s ↦ x₀ + ∫ u in (0 : ℝ)..s, v u) (v t) t := by
    have h := (hasDerivAt_const (𝕜 := ℝ) t x₀).add
      (hv.integral_hasStrictDerivAt 0 t).hasDerivAt
    convert h using 1
    · funext s
      rfl
    · simp
  apply hprimitive.hasDerivWithinAt.congr_of_eventuallyEq
  · have hIio : Set.Iio (1 : ℝ) ∈ nhdsWithin t (Set.Ici t) :=
      (show nhdsWithin t (Set.Ici t) ≤ nhds t from inf_le_left) (Iio_mem_nhds ht.2)
    filter_upwards [hIio, self_mem_nhdsWithin] with s hs hts
    rw [Set.projIcc_of_mem zero_le_one ⟨ht.1.trans hts, hs.le⟩]
    exact hq ⟨s, ht.1.trans hts, hs.le⟩
  · rw [Set.projIcc_of_mem zero_le_one ⟨ht.1, ht.2.le⟩]
    exact hq ⟨t, ht.1, ht.2.le⟩

/-- A smooth parameterized autonomous vector field which vanishes at the base parameter admits a
locally smooth family of solutions through a fixed initial state. The result is stated at every
finite order; this is the form needed to assemble smoothness of a germ. Each nearby path satisfies
the Picard integral equation, the corresponding ODE at every interior time, and its right-hand
version at the initial endpoint. -/
theorem exists_contDiffAt_picard_solution
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (n : ℕ) (f : E × F → F) (p₀ : E) (x₀ : F)
    (hf : ContDiffAt ℝ (n + 1) f (p₀, x₀))
    (hzero : ∀ y, f (p₀, y) = 0) :
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
  obtain ⟨g, hg, hgf⟩ :=
    exists_contDiff_eventuallyEq_of_finiteDimensional (n + 1) hf
  let gc : C(E × F, F) := ⟨g, hg.continuous⟩
  let R := picardResidual gc x₀
  let basePath : C(Set.Icc (0 : ℝ) 1, F) := ContinuousMap.const _ x₀
  let u : E × C(Set.Icc (0 : ℝ) 1, F) := (p₀, basePath)
  have hR : ContDiffAt ℝ (n + 1) R u :=
    (contDiff_picardResidual (n + 1) gc hg x₀).contDiffAt
  have hgfBase : g (p₀, x₀) = f (p₀, x₀) :=
    hgf.self_of_nhds
  have hgzero : ∀ᶠ y in nhds x₀, gc (p₀, y) = 0 := by
    have hpull : ∀ᶠ y in nhds x₀, g (p₀, y) = f (p₀, y) :=
      (continuousAt_const.prodMk continuousAt_id).eventually hgf
    filter_upwards [hpull] with y hy
    exact hy.trans (hzero y)
  have hpartial := hasStrictFDerivAt_picardResidual_parameter gc p₀ x₀ hgzero
  have hdiff := hR.differentiableAt (by norm_num)
  have hinnerRaw := hasFDerivAt_const (𝕜 := ℝ) p₀ basePath |>.prodMk
    (hasFDerivAt_id (𝕜 := ℝ) basePath)
  have hinner := hinnerRaw.congr_fderiv (g' :=
    ContinuousLinearMap.inr ℝ E C(Set.Icc (0 : ℝ) 1, F)) (by
      apply ContinuousLinearMap.ext
      intro z
      simp [ContinuousLinearMap.inr_apply])
  have hpartialFromR := hdiff.hasFDerivAt.comp basePath hinner
  have hpartialEq := hpartialFromR.unique hpartial.hasFDerivAt
  have hinvertible :
      (fderiv ℝ R u ∘L
        ContinuousLinearMap.inr ℝ E C(Set.Icc (0 : ℝ) 1, F)).IsInvertible := by
    rw [hpartialEq]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  let γ : E → C(Set.Icc (0 : ℝ) 1, F) :=
    hR.implicitFunction (by norm_num) hinvertible
  have hγsmooth : ContDiffAt ℝ (n + 1) γ p₀ :=
    hR.contDiffAt_implicitFunction (by norm_num) hinvertible
  have hγbase : γ p₀ = basePath :=
    hR.implicitFunction_apply_self (by norm_num) hinvertible
  have hRbase : R u = 0 := by
    have hcomp : gc.comp (parameterizedPath u) = 0 := by
      ext t
      simp only [gc, u, basePath]
      exact hgfBase.trans (hzero x₀)
    simp only [R, picardResidual, u, basePath, hcomp, map_zero, sub_self]
  have hγeq : ∀ᶠ p in nhds p₀, R (p, γ p) = 0 := by
    filter_upwards [hR.eventually_apply_implicitFunction (by norm_num) hinvertible] with p hp
    rw [hp, hRbase]
  have hpath := parameterizedPath.continuous.continuousAt.comp
    (continuousAt_id.prodMk hγsmooth.continuousAt)
  have hpathBase : parameterizedPath (p₀, γ p₀) =
      ContinuousMap.const _ (p₀, x₀) := by
    rw [hγbase]
    ext t <;> rfl
  have hgfSet : {z : E × F | g z = f z} ∈ nhds (p₀, x₀) := hgf
  obtain ⟨ε, hε, hεgf⟩ := Metric.mem_nhds_iff.mp hgfSet
  have hpathsNear : ∀ᶠ p in nhds p₀,
      dist (parameterizedPath (p, γ p)) (ContinuousMap.const _ (p₀, x₀)) < ε := by
    have hnear := hpath (Metric.ball_mem_nhds
      (parameterizedPath (p₀, γ p₀)) hε)
    filter_upwards [hnear] with p hp
    change parameterizedPath (p, γ p) ∈
      Metric.ball (parameterizedPath (p₀, γ p₀)) ε at hp
    rw [Metric.mem_ball] at hp
    simpa only [hpathBase] using hp
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
  have hpathEq : γ p = ContinuousMap.const _ x₀ +
      ContinuousMap.unitIntervalIntegral (gc.comp (parameterizedPath (p, γ p))) := by
    apply sub_eq_zero.mp
    calc
      γ p - (ContinuousMap.const _ x₀ +
          ContinuousMap.unitIntervalIntegral (gc.comp (parameterizedPath (p, γ p)))) =
          R (p, γ p) := by
        simp only [R, picardResidual]
        abel
      _ = 0 := hp
  have hpicard : ∀ t : Set.Icc (0 : ℝ) 1,
      γ p t = x₀ + ∫ s in (0 : ℝ)..t,
        gc (p, γ p (Set.projIcc 0 1 zero_le_one s)) := by
    intro t
    have ht := congrArg (fun q : C(Set.Icc (0 : ℝ) 1, F) ↦ q t) hpathEq
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply,
      ContinuousMap.unitIntervalIntegral_apply, ContinuousMap.comp_apply,
      parameterizedPath_apply] using ht
  refine ⟨fun t ↦ (hpicard t).trans (congrArg (x₀ + ·) ?_), ?_, ?_⟩
  · apply intervalIntegral.integral_congr
    intro s _
    exact hpoint (Set.projIcc 0 1 zero_le_one s)
  · intro t ht
    have hcontinuous : Continuous (fun s : ℝ ↦
        gc (p, γ p (Set.projIcc 0 1 zero_le_one s))) :=
      gc.continuous.comp
        (continuous_const.prodMk ((γ p).continuous.comp continuous_projIcc))
    have hderiv := hasDerivAt_of_forall_eq_picard
      (fun s : ℝ ↦ gc (p, γ p (Set.projIcc 0 1 zero_le_one s)))
      hcontinuous x₀ (γ p) hpicard ht
    exact hderiv.congr_deriv (hpoint (Set.projIcc 0 1 zero_le_one t))
  · intro t ht
    have hcontinuous : Continuous (fun s : ℝ ↦
        gc (p, γ p (Set.projIcc 0 1 zero_le_one s))) :=
      gc.continuous.comp
        (continuous_const.prodMk ((γ p).continuous.comp continuous_projIcc))
    have hderiv := hasDerivWithinAt_Ici_of_forall_eq_picard
      (fun s : ℝ ↦ gc (p, γ p (Set.projIcc 0 1 zero_le_one s)))
      hcontinuous x₀ (γ p) hpicard ht
    exact hderiv.congr_deriv (hpoint (Set.projIcc 0 1 zero_le_one t))

end ODE
