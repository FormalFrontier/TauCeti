/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Extending finite-dimensional smooth germs

A function which is smooth, of finite or infinite order, on a neighbourhood of a point of a
finite-dimensional real normed space agrees near that point with a globally smooth function of
the same order. A smooth bump function performs the extension while preserving the original
function near the base point. Since the bump is compactly supported, so is the representative,
and a representative of order at least one is moreover globally Lipschitz.

These general calculus lemmas are used by the parameter-dependent ODE construction for the
Lie-group exponential, and by the construction of a local flow out of the global solution of a
globally Lipschitz field.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function which is smooth on a neighbourhood of a point of a finite-dimensional real normed
space agrees near that point with a compactly supported globally smooth function of the same
order. -/
theorem ContDiffOn.exists_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] {n : ℕ∞} {f : E → F} {x : E} {s : Set E}
    (hfs : ContDiffOn ℝ n f s) (hs : s ∈ nhds x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f := by
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
  refine ⟨g, hg, b.hasCompactSupport.smul_right, ?_⟩
  filter_upwards [b.eventuallyEq_one] with y hy
  have hone : (fun _ : E ↦ (1 : ℝ)) y = 1 := by
    rfl
  have hy' : b y = 1 := hy.trans hone
  simp only [g, hy', one_smul]

/-- A finite-order smooth germ on a finite-dimensional real normed space has a compactly supported
globally smooth representative of the same order. -/
theorem ContDiffAt.exists_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] (n : ℕ) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f :=
  let ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by simp)
  hfs.exists_contDiff_eventuallyEq_of_finiteDimensional hs

/-- A function which is smooth of order at least one on a neighbourhood of a point of a
finite-dimensional real normed space agrees near that point with a globally smooth **and globally
Lipschitz** function of the same order: the compactly supported representative above has a bounded
derivative. -/
theorem ContDiffOn.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] {n : ℕ∞} {f : E → F} {x : E} {s : Set E}
    (hf : ContDiffOn ℝ (n + 1) f s) (hs : s ∈ nhds x) :
    ∃ (g : E → F) (K : NNReal), ContDiff ℝ (n + 1) g ∧ LipschitzWith K g ∧ g =ᶠ[nhds x] f := by
  obtain ⟨g, hg, hgsupp, hgf⟩ := hf.exists_contDiff_eventuallyEq_of_finiteDimensional hs
  have hone : ((n : WithTop ℕ∞) + 1) ≠ 0 := by simp
  obtain ⟨C, hC⟩ := (hg.continuous_fderiv hone).bounded_above_of_compact_support
    (hgsupp.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x)
  refine ⟨g, C.toNNReal, hg, lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable hone) ?_, hgf⟩
  intro y
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC0]
  exact hC y
