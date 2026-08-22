/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
public import TauCeti.Analysis.InnerProductSpace.NormPow
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The Newtonian kernel in dimension at least three

For `3 ≤ n`, this file defines the Newtonian kernel for the negative Laplacian on
`EuclideanSpace ℝ (Fin n)`:

`Gₙ(x) = (n (n - 2) ωₙ)⁻¹ ‖x‖²⁻ⁿ`,

where `ωₙ` is the volume of the Euclidean unit ball.  It proves the full Fréchet derivative
formula and the pointwise equation `Δ Gₙ = 0` away from the pole, together with translated
versions for a pole at an arbitrary point.  The dimension-three specialization recovers the
classical kernel `1 / (4π‖x‖)`.

The normalization and formulas follow Evans, *Partial Differential Equations*, Section 2.2.
The remaining distributional identity `-Δ Gₙ = δ₀` will use the sphere-flux calculation built
from the derivative proved here.

## Main declarations

* `TauCeti.newtonianKernel`: the normalized kernel in dimension `n ≥ 3`.
* `TauCeti.hasFDerivAt_newtonianKernel`: its derivative away from the origin.
* `TauCeti.norm_fderiv_newtonianKernel`: the `‖x‖ ^ (1 - n)` operator norm of that derivative.
* `TauCeti.laplacian_newtonianKernel`: the pointwise equation `Δ Gₙ = 0` away from the origin.
* `TauCeti.harmonicAt_newtonianKernel_sub`: harmonicity of the kernel with a translated pole.
* `TauCeti.newtonianKernel_three`: the familiar three-dimensional formula.
-/

public section

noncomputable section

namespace TauCeti

open Filter InnerProductSpace Laplacian MeasureTheory Metric Topology

open scoped RealInnerProductSpace

/-- The Newtonian kernel for the negative Laplacian on `ℝⁿ`.

For `3 ≤ n`, this normalization is the fundamental solution, and the exponent `2 - n` is
negative.  Lean's convention for a negative real power of zero makes the kernel take the value
zero at the pole in these dimensions.  Results that need the higher-dimensional regime state it
as a hypothesis rather than carrying it in the definition. -/
def newtonianKernel (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ((n : ℝ) * ((n : ℝ) - 2) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
    ‖x‖ ^ (2 - (n : ℝ))

/-- The defining formula for the Newtonian kernel.  The body of `TauCeti.newtonianKernel` is not
`@[expose]`d, so this is the form in which other modules reach the definition. -/
theorem newtonianKernel_def (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    newtonianKernel n x =
      ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
      ‖x‖ ^ (2 - (n : ℝ)) := by
  rw [newtonianKernel]

/-- The totalized Newtonian kernel takes the value zero at its pole. -/
@[simp]
theorem newtonianKernel_zero (n : ℕ) :
    newtonianKernel n 0 = 0 := by
  rcases eq_or_ne n 2 with rfl | hn
  · norm_num [newtonianKernel]
  · have hexp : 2 - (n : ℝ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hn.symm)
    simp [newtonianKernel, Real.zero_rpow hexp]

/-- The Newtonian kernel is radial, hence invariant under orthogonal transformations. -/
@[simp]
theorem newtonianKernel_map_linearIsometryEquiv (n : ℕ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    newtonianKernel n (e x) = newtonianKernel n x := by
  simp [newtonianKernel]

/-- The Newtonian kernel is symmetric under exchanging a point and its pole. -/
theorem newtonianKernel_sub_comm (n : ℕ) (x a : EuclideanSpace ℝ (Fin n)) :
    newtonianKernel n (x - a) = newtonianKernel n (a - x) := by
  simp [newtonianKernel, norm_sub_rev]

/-- Real dilation scales the Newtonian kernel with radial homogeneity `2 - n`. -/
theorem newtonianKernel_smul (n : ℕ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    newtonianKernel n (r • x) = ‖r‖ ^ (2 - (n : ℝ)) * newtonianKernel n x := by
  rw [newtonianKernel_def, newtonianKernel_def, norm_smul,
    Real.mul_rpow (norm_nonneg r) (norm_nonneg x)]
  ring

/-- The Euclidean unit ball has positive real volume in every dimension. -/
theorem volume_real_unitBall_pos (n : ℕ) :
    0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  exact ENNReal.toReal_pos
    (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) zero_lt_one).ne'
    measure_ball_ne_top

/-- Away from the pole, the normalized Newtonian kernel is strictly positive. -/
theorem newtonianKernel_pos (n : ℕ) (hn : 3 ≤ n)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    0 < newtonianKernel n x := by
  have hnℝ : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hnsub : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  rw [newtonianKernel_def]
  exact mul_pos (inv_pos.mpr (mul_pos (mul_pos hnpos hnsub)
      (volume_real_unitBall_pos n)))
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _)

/-- The Fréchet derivative of the Newtonian kernel away from its pole. -/
theorem hasFDerivAt_newtonianKernel (n : ℕ) (hn : n ≠ 2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    HasFDerivAt (newtonianKernel n)
      ((-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
        ‖x‖ ^ (-(n : ℝ))) • innerSL ℝ x) x := by
  have hfun : newtonianKernel n = fun y ↦
      ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
      ‖y‖ ^ (2 - (n : ℝ)) := by rfl
  rw [hfun]
  refine ((hasFDerivAt_norm_rpow_of_ne (2 - (n : ℝ)) hx).const_mul
    (((n : ℝ) * ((n : ℝ) - 2) *
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹)).congr_fderiv ?_
  have hn0 : (n : ℝ) ≠ 0 := by
    cases n with
    | zero => exact (hx (Subsingleton.elim x 0)).elim
    | succ n => positivity
  have hn2 : (n : ℝ) - 2 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hn)
  have hvol := (volume_real_unitBall_pos n).ne'
  have hexp : (2 - (n : ℝ)) - 2 = -(n : ℝ) := by ring
  rw [hexp]
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  field_simp
  ring

/-- The Fréchet derivative of the Newtonian kernel as a continuous linear functional. -/
theorem fderiv_newtonianKernel (n : ℕ) (hn : n ≠ 2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    fderiv ℝ (newtonianKernel n) x =
      (-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
        ‖x‖ ^ (-(n : ℝ))) • innerSL ℝ x :=
  (hasFDerivAt_newtonianKernel n hn hx).fderiv

/-- The derivative of the Newtonian kernel evaluated in a direction. -/
theorem fderiv_newtonianKernel_apply (n : ℕ) (hn : n ≠ 2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (newtonianKernel n) x v =
      -(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ‖x‖ ^ (-(n : ℝ)) * ⟪x, v⟫_ℝ) := by
  rw [fderiv_newtonianKernel n hn hx]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

/-- The operator norm of the derivative of the Newtonian kernel decays like `‖x‖ ^ (1 - n)`. -/
@[simp]
theorem norm_fderiv_newtonianKernel (n : ℕ) (hn : n ≠ 2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ‖fderiv ℝ (newtonianKernel n) x‖ =
      ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ‖x‖ ^ (1 - (n : ℝ)) := by
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    exact hx (Subsingleton.elim x 0)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsplit : ‖x‖ ^ (1 - (n : ℝ)) = ‖x‖ ^ (-(n : ℝ)) * ‖x‖ := by
    rw [sub_eq_add_neg, add_comm, Real.rpow_add hnorm, Real.rpow_one]
  rw [fderiv_newtonianKernel n hn hx, norm_smul, innerSL_apply_norm, Real.norm_eq_abs,
    abs_mul, abs_neg, abs_inv, abs_of_pos (mul_pos hnpos (volume_real_unitBall_pos n)),
    abs_of_pos (Real.rpow_pos_of_pos hnorm _), hsplit]
  ring

/-- Away from its pole, the Newtonian kernel is twice continuously differentiable. -/
theorem contDiffAt_newtonianKernel (n : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (newtonianKernel n) x := by
  have hfun : newtonianKernel n =
      ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ •
        fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (2 - (n : ℝ)) := by
    funext y
    simp only [newtonianKernel_def, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  have hpow : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) ↦
      ‖y‖ ^ (2 - (n : ℝ))) x :=
    (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
  exact hpow.const_smul (((n : ℝ) * ((n : ℝ) - 2) *
    volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹)

/-- The Newtonian kernel solves the homogeneous Laplace equation pointwise away from its pole. -/
@[simp]
theorem laplacian_newtonianKernel (n : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    Δ (newtonianKernel n) x = 0 := by
  have hfun : newtonianKernel n =
      ((n : ℝ) * ((n : ℝ) - 2) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ •
        fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖ ^ (2 - (n : ℝ)) := by
    funext y
    simp only [newtonianKernel_def, Pi.smul_apply, smul_eq_mul]
  have hpow : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) ↦
      ‖y‖ ^ (2 - (n : ℝ))) x :=
    (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
  rw [hfun, laplacian_smul _ hpow]
  rw [laplacian_norm_rpow_of_ne (2 - (n : ℝ)) hx]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  ring

/-- The Newtonian kernel is harmonic at every point away from its pole at the origin. -/
theorem harmonicAt_newtonianKernel (n : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    HarmonicAt (newtonianKernel n) x := by
  refine ⟨contDiffAt_newtonianKernel n hx, ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact laplacian_newtonianKernel n hy

/-- The Newtonian kernel is harmonic on the punctured Euclidean space. -/
theorem harmonicOnNhd_newtonianKernel (n : ℕ) :
    HarmonicOnNhd (newtonianKernel n) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
  intro x hx
  exact harmonicAt_newtonianKernel n (Set.mem_compl_singleton_iff.mp hx)

/-- A Newtonian kernel with pole at `a` is harmonic away from that pole. -/
theorem harmonicAt_newtonianKernel_sub (n : ℕ)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) :
    HarmonicAt (fun y ↦ newtonianKernel n (y - a)) x := by
  simpa [sub_eq_add_neg] using
    (harmonicAt_comp_add_right_iff (f := newtonianKernel n) (x := x) (a := -a)).2
      (harmonicAt_newtonianKernel n (sub_ne_zero.mpr hxa))

/-- A Newtonian kernel with pole at `a` is twice continuously differentiable away from `a`. -/
theorem contDiffAt_newtonianKernel_sub (n : ℕ)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) :
    ContDiffAt ℝ 2 (fun y ↦ newtonianKernel n (y - a)) x :=
  (harmonicAt_newtonianKernel_sub n hxa).1

/-- A Newtonian kernel with pole at `a` has the translated Fréchet derivative. -/
theorem hasFDerivAt_newtonianKernel_sub (n : ℕ) (hn : n ≠ 2)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) :
    HasFDerivAt (fun y ↦ newtonianKernel n (y - a))
      ((-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
        ‖x - a‖ ^ (-(n : ℝ))) • innerSL ℝ (x - a)) x := by
  rw [hasFDerivAt_comp_sub]
  exact hasFDerivAt_newtonianKernel n hn (sub_ne_zero.mpr hxa)

/-- The Fréchet derivative of a Newtonian kernel with pole at `a`. -/
theorem fderiv_newtonianKernel_sub (n : ℕ) (hn : n ≠ 2)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) :
    fderiv ℝ (fun y ↦ newtonianKernel n (y - a)) x =
      (-(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹) *
        ‖x - a‖ ^ (-(n : ℝ))) • innerSL ℝ (x - a) :=
  (hasFDerivAt_newtonianKernel_sub n hn hxa).fderiv

/-- The derivative of the Newtonian kernel with a translated pole. -/
theorem fderiv_newtonianKernel_sub_apply (n : ℕ) (hn : n ≠ 2)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y ↦ newtonianKernel n (y - a)) x v =
      -(((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ‖x - a‖ ^ (-(n : ℝ)) * ⟪x - a, v⟫_ℝ) := by
  rw [fderiv_newtonianKernel_sub n hn hxa]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

/-- The operator norm of the derivative of a Newtonian kernel with pole at `a`. -/
@[simp]
theorem norm_fderiv_newtonianKernel_sub (n : ℕ) (hn : n ≠ 2)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) :
    ‖fderiv ℝ (fun y ↦ newtonianKernel n (y - a)) x‖ =
      ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        ‖x - a‖ ^ (1 - (n : ℝ)) := by
  rw [fderiv_comp_sub]
  exact norm_fderiv_newtonianKernel n hn (sub_ne_zero.mpr hxa)

/-- A translated Newtonian kernel solves the homogeneous Laplace equation away from its pole. -/
@[simp]
theorem laplacian_newtonianKernel_sub (n : ℕ)
    {x a : EuclideanSpace ℝ (Fin n)} (hxa : x ≠ a) :
    Δ (fun y ↦ newtonianKernel n (y - a)) x = 0 :=
  (harmonicAt_newtonianKernel_sub n hxa).2.self_of_nhds

/-- A Newtonian kernel with pole at `a` is harmonic on the complement of the pole. -/
theorem harmonicOnNhd_newtonianKernel_sub (n : ℕ)
    (a : EuclideanSpace ℝ (Fin n)) :
    HarmonicOnNhd (fun x ↦ newtonianKernel n (x - a)) ({a}ᶜ : Set _) := by
  intro x hx
  exact harmonicAt_newtonianKernel_sub n (Set.mem_compl_singleton_iff.mp hx)

/-- In dimension three the Newtonian kernel is the classical function `1 / (4π‖x‖)`. -/
theorem newtonianKernel_three (x : EuclideanSpace ℝ (Fin 3)) :
    newtonianKernel 3 x = (4 * Real.pi * ‖x‖)⁻¹ := by
  have hvol : volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      Real.pi * 4 / 3 := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three]
    simp only [one_pow, ENNReal.ofReal_one, one_mul]
    exact ENNReal.toReal_ofReal (by positivity)
  rw [newtonianKernel_def, hvol]
  norm_num [Real.rpow_neg_one]
  field_simp [Real.pi_ne_zero]

end TauCeti

end
