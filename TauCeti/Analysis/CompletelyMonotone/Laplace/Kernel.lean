/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Probability.Kernel.Defs

/-!
# The Laplace kernel on `ℝ≥0`

The exponential kernel `p ↦ e^{-xp}` of the Laplace transform on `ℝ≥0`, as a plain function
and as a bundled bounded continuous function, together with its basic bounds and its
integrability against finite measures. Integrating that exponential kernel against each fibre
of a *transition* kernel into `ℝ≥0` gives the fibrewise Laplace transform, which is also set up
here. This lightweight module is shared by the Chafaï approximating-measure machinery and the
Laplace-representation theory, which otherwise do not depend on each other.

## Main declarations

* `TauCeti.laplaceKernelBoundedContinuous`: the kernel as a bounded continuous function.
* `TauCeti.integrable_exp_neg_mul`: the kernel is integrable against any finite measure.
* `TauCeti.kernelLaplaceTransform`: the fibrewise Laplace transform
  `q ↦ ∫⁻ p, exp (-t p) ∂(κ q)` of a transition kernel `κ` into `ℝ≥0`, with its measurability,
  its value at time `0`, and its monotonicity and finiteness bounds.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction ENNReal NNReal

namespace TauCeti

/-- The Laplace kernel `p ↦ e^{-tp}` is continuous in the coordinate variable. -/
lemma continuous_exp_neg_mul (t : ℝ) :
    Continuous fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))) := by
  fun_prop

/-- For `0 ≤ x` the Laplace kernel is bounded by `1` on `ℝ≥0`. -/
lemma exp_neg_mul_le_one {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    Real.exp (-(x * (p : ℝ))) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg hx p.coe_nonneg)

/-- The Laplace kernel as a bundled bounded continuous test function of the nonnegative
variable `p`, for fixed nonnegative `x`. -/
noncomputable def laplaceKernelBoundedContinuous {x : ℝ} (hx : 0 ≤ x) : ℝ≥0 →ᵇ ℝ where
  toFun := fun p => Real.exp (-(x * (p : ℝ)))
  continuous_toFun := continuous_exp_neg_mul x
  map_bounded' :=
    ⟨1, fun p q => by
      rw [Real.dist_eq]
      have hp0 : 0 < Real.exp (-(x * (p : ℝ))) := Real.exp_pos _
      have hp1 := exp_neg_mul_le_one hx p
      have hq0 : 0 < Real.exp (-(x * (q : ℝ))) := Real.exp_pos _
      have hq1 := exp_neg_mul_le_one hx q
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩⟩

/-- The bundled Laplace kernel evaluates to the usual exponential kernel on `ℝ≥0`. -/
@[simp]
lemma laplaceKernelBoundedContinuous_apply {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    laplaceKernelBoundedContinuous hx p = Real.exp (-(x * (p : ℝ))) := by
  rw [laplaceKernelBoundedContinuous]; rfl

/-- **The Laplace kernel is integrable against a finite measure.** For `0 ≤ x` the kernel
`p ↦ e^{-xp}` is bounded and continuous on `ℝ≥0`, hence integrable against any finite measure. -/
lemma integrable_exp_neg_mul (μ : Measure ℝ≥0) [IsFiniteMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) μ := by
  have h := (laplaceKernelBoundedContinuous hx).integrable μ
  rwa [funext (laplaceKernelBoundedContinuous_apply hx)] at h

/-! ## The fibrewise Laplace transform of a kernel -/

section Transform

variable {V : Type*} [MeasurableSpace V]

/-- The **fibrewise Laplace transform** of a kernel `κ` from `V` to `ℝ≥0`: the function
`q ↦ ∫⁻ p, exp (-t p) ∂(κ q)` on `V`. It is the density that turns a spatial measure into the
time-`t` spatial slice of the assembled measure on `ℝ≥0 × V`
(`TauCeti.spatialSlice_timeKernelMeasure`). -/
noncomputable def kernelLaplaceTransform (κ : Kernel V ℝ≥0) (t : ℝ≥0) (q : V) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (Real.exp (-(t : ℝ) * (p : ℝ))) ∂(κ q)

/-- The defining formula for `TauCeti.kernelLaplaceTransform`. Not `@[simp]`: simp should not
unfold the abstraction into a raw integral. -/
theorem kernelLaplaceTransform_apply (κ : Kernel V ℝ≥0) (t : ℝ≥0) (q : V) :
    kernelLaplaceTransform κ t q = ∫⁻ p, ENNReal.ofReal (Real.exp (-(t : ℝ) * (p : ℝ))) ∂(κ q) :=
  (rfl)

@[fun_prop]
theorem measurable_kernelLaplaceTransform (κ : Kernel V ℝ≥0) (t : ℝ≥0) :
    Measurable (kernelLaplaceTransform κ t) := by
  unfold kernelLaplaceTransform
  fun_prop

/-- At time `0` the exponential weight is trivial, so the fibrewise Laplace transform is the
fibrewise total mass. -/
@[simp]
theorem kernelLaplaceTransform_zero (κ : Kernel V ℝ≥0) (q : V) :
    kernelLaplaceTransform κ 0 q = κ q Set.univ := by
  rw [kernelLaplaceTransform_apply]
  simp

/-- A Markov kernel has fibrewise Laplace transform `1` at time `0`. -/
theorem kernelLaplaceTransform_zero_of_isMarkovKernel (κ : Kernel V ℝ≥0) [IsMarkovKernel κ] :
    kernelLaplaceTransform κ 0 = 1 := by
  funext q
  rw [kernelLaplaceTransform_zero, measure_univ, Pi.one_apply]

/-- The fibrewise Laplace transform is bounded by the fibrewise total mass. -/
theorem kernelLaplaceTransform_le (κ : Kernel V ℝ≥0) (t : ℝ≥0) (q : V) :
    kernelLaplaceTransform κ t q ≤ κ q Set.univ := by
  rw [kernelLaplaceTransform_apply, ← kernelLaplaceTransform_zero κ q,
    kernelLaplaceTransform_apply]
  refine lintegral_mono fun p => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  simpa using mul_nonneg t.coe_nonneg p.coe_nonneg

/-- The fibrewise Laplace transform decreases in time: the weight `exp (-t p)` is nonincreasing
in `t` at every nonnegative frequency `p`. -/
theorem kernelLaplaceTransform_antitone (κ : Kernel V ℝ≥0) (q : V) :
    Antitone fun t : ℝ≥0 => kernelLaplaceTransform κ t q := by
  intro t u htu
  refine lintegral_mono fun p => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonneg_right (neg_le_neg (mod_cast htu)) p.coe_nonneg

/-- The fibrewise Laplace transform is finite against a finite kernel. -/
theorem kernelLaplaceTransform_ne_top (κ : Kernel V ℝ≥0) [IsFiniteKernel κ] (t : ℝ≥0) (q : V) :
    kernelLaplaceTransform κ t q ≠ ⊤ :=
  ((kernelLaplaceTransform_le κ t q).trans_lt (measure_lt_top _ _)).ne

end Transform

end TauCeti
