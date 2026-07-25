/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# The planar Newtonian kernel away from its pole

This file introduces the logarithmic kernel for the negative Laplacian on the complex plane,

`G(z) = -(2 * π)⁻¹ * log ‖z‖`,

and establishes its classical pointwise properties away from the pole.  In particular, `G` and
each translate `z ↦ G (z - a)` are harmonic away from their poles.  The distributional identity
`-Δ G = δ₀`, which fixes the normalization by computing the flux through a circle, is deliberately
left to the later distributional development of the fundamental solution.

The harmonicity proof consumes Mathlib's `AnalyticAt.harmonicAt_log_norm`, applied to the identity
or to `z ↦ z - a`.  The remaining results record the translation, symmetry, and scaling API used
when the kernel is integrated against a source to form a Newtonian potential.

## Main declarations

* `TauCeti.planarNewtonianKernel`: the logarithmic kernel for `-Δ` on `ℂ`.
* `TauCeti.harmonicAt_planarNewtonianKernel`: harmonicity away from the origin.
* `TauCeti.harmonicAt_planarNewtonianKernel_sub`: harmonicity of a kernel with pole `a`.
* `TauCeti.laplacian_planarNewtonianKernel`: the pointwise equation `Δ G = 0` off the pole.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian

/-- The Newtonian kernel for the negative Laplacian on the plane, represented as `ℂ`.

The value assigned at the pole is immaterial for the pointwise theory in this file.  Lean's
convention `Real.log 0 = 0` makes this a total function; analytically, the kernel has a logarithmic
singularity there. -/
def planarNewtonianKernel (z : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * Real.log ‖z‖

/-- The defining formula for the planar Newtonian kernel. -/
theorem planarNewtonianKernel_def (z : ℂ) :
    planarNewtonianKernel z = -(2 * Real.pi)⁻¹ * Real.log ‖z‖ := by
  rw [planarNewtonianKernel]

@[simp]
theorem planarNewtonianKernel_zero : planarNewtonianKernel 0 = 0 := by
  simp [planarNewtonianKernel]

@[simp]
theorem planarNewtonianKernel_neg (z : ℂ) :
    planarNewtonianKernel (-z) = planarNewtonianKernel z := by
  simp [planarNewtonianKernel]

/-- The planar Newtonian kernel is invariant under multiplication by a unit complex number. -/
theorem planarNewtonianKernel_unit_mul {u z : ℂ} (hu : ‖u‖ = 1) :
    planarNewtonianKernel (u * z) = planarNewtonianKernel z := by
  simp [planarNewtonianKernel, hu]

/-- Scaling the argument adds the logarithm of the scale to the planar Newtonian kernel. -/
theorem planarNewtonianKernel_mul (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    planarNewtonianKernel (z * w) = planarNewtonianKernel z + planarNewtonianKernel w := by
  rw [planarNewtonianKernel, planarNewtonianKernel, planarNewtonianKernel, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hw)]
  ring

/-- The kernel with pole `a` is symmetric in its two spatial arguments. -/
theorem planarNewtonianKernel_sub_comm (z a : ℂ) :
    planarNewtonianKernel (z - a) = planarNewtonianKernel (a - z) := by
  rw [← neg_sub a z, planarNewtonianKernel_neg]

/-- The translated kernel `z ↦ G(z - a)` is harmonic at every point other than its pole `a`. -/
theorem harmonicAt_planarNewtonianKernel_sub {z a : ℂ} (hza : z ≠ a) :
    HarmonicAt (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z := by
  have hana : AnalyticAt ℂ (fun w : ℂ ↦ w - a) z := analyticAt_id.sub analyticAt_const
  have hne : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hlog : HarmonicAt (fun w : ℂ ↦ Real.log ‖w - a‖) z :=
    hana.harmonicAt_log_norm hne
  have hkernel :
      (fun w : ℂ ↦ planarNewtonianKernel (w - a)) =
        (-(2 * Real.pi)⁻¹ : ℝ) • fun w : ℂ ↦ Real.log ‖w - a‖ := by
    funext w
    simp only [planarNewtonianKernel_def, Pi.smul_apply, smul_eq_mul]
  rw [hkernel]
  exact hlog.const_smul

/-- The logarithmic Newtonian kernel is harmonic at every point away from its pole at `0`. -/
theorem harmonicAt_planarNewtonianKernel {z : ℂ} (hz : z ≠ 0) :
    HarmonicAt planarNewtonianKernel z := by
  simpa only [sub_zero] using
    (harmonicAt_planarNewtonianKernel_sub (z := z) (a := 0) hz)

/-- The planar Newtonian kernel is harmonic on the punctured plane. -/
theorem harmonicOnNhd_planarNewtonianKernel :
    HarmonicOnNhd planarNewtonianKernel ({0}ᶜ : Set ℂ) := by
  intro z hz
  exact harmonicAt_planarNewtonianKernel (Set.mem_compl_singleton_iff.mp hz)

/-- A planar Newtonian kernel with pole `a` is harmonic on the complement of that pole. -/
theorem harmonicOnNhd_planarNewtonianKernel_sub (a : ℂ) :
    HarmonicOnNhd (fun z : ℂ ↦ planarNewtonianKernel (z - a)) ({a}ᶜ : Set ℂ) := by
  intro z hz
  exact harmonicAt_planarNewtonianKernel_sub (Set.mem_compl_singleton_iff.mp hz)

/-- Away from its pole, a translated planar Newtonian kernel is twice continuously
differentiable. -/
theorem contDiffAt_planarNewtonianKernel_sub {z a : ℂ} (hza : z ≠ a) :
    ContDiffAt ℝ 2 (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z :=
  (harmonicAt_planarNewtonianKernel_sub hza).1

/-- Away from its pole, the planar Newtonian kernel is twice continuously differentiable. -/
theorem contDiffAt_planarNewtonianKernel {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ 2 planarNewtonianKernel z := by
  simpa only [sub_zero] using
    (contDiffAt_planarNewtonianKernel_sub (z := z) (a := 0) hz)

/-- The planar Newtonian kernel solves the homogeneous Laplace equation pointwise away from its
pole.  Its nonzero distributional Laplacian is concentrated at the omitted pole. -/
@[simp]
theorem laplacian_planarNewtonianKernel {z : ℂ} (hz : z ≠ 0) :
    Δ planarNewtonianKernel z = 0 := by
  exact (harmonicAt_planarNewtonianKernel hz).2.self_of_nhds

/-- A translated planar Newtonian kernel solves the homogeneous Laplace equation away from its
pole. -/
@[simp]
theorem laplacian_planarNewtonianKernel_sub {z a : ℂ} (hza : z ≠ a) :
    Δ (fun w : ℂ ↦ planarNewtonianKernel (w - a)) z = 0 := by
  exact (harmonicAt_planarNewtonianKernel_sub hza).2.self_of_nhds

end TauCeti

end
