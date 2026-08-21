/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Extending finite-dimensional smooth germs

A finite-order smooth germ on a finite-dimensional real normed space can be represented by a
globally smooth function of the same order. A smooth bump function performs the extension while
preserving the original function near the base point.

This general calculus lemma is used by the parameter-dependent ODE construction for the Lie-group
exponential.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite-order smooth germ on a finite-dimensional real normed space has a globally smooth
representative of the same order. -/
theorem ContDiffAt.exists_contDiff_eventuallyEq_of_finiteDimensional
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
  have hone : (fun _ : E ↦ (1 : ℝ)) y = 1 := by
    rfl
  have hy' : b y = 1 := hy.trans hone
  simp only [g, hy', one_smul]
