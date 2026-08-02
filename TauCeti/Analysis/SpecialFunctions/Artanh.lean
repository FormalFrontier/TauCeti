/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The calculus of the inverse hyperbolic tangent

Mathlib's `Analysis/SpecialFunctions/Artanh.lean` introduces `Real.artanh` and proves that it
inverts `Real.tanh` on `(-1, 1)`, that it is strictly monotone there, and the closed forms
`Real.sinh_artanh`, `Real.cosh_artanh`. It records no analytic property whatsoever: neither
continuity nor differentiability of `Real.artanh` appears anywhere in the pinned Mathlib.

This file supplies that missing calculus. Everything follows from the logarithmic formula
`Real.artanh_eq_half_log`, `artanh x = (1 / 2) * log ((1 + x) / (1 - x))`, which is valid on
the open interval `(-1, 1)`; since that interval is open, the formula may be differentiated at
each of its points and the result transported back to `Real.artanh` itself.

## Main declarations

* `Real.hasDerivAt_artanh` — `Real.artanh` has derivative `(1 - x ^ 2)⁻¹` at each `x` of
  `(-1, 1)`, with `Real.deriv_artanh`, `Real.differentiableAt_artanh`,
  `Real.differentiableOn_artanh`, `Real.continuousAt_artanh` and `Real.continuousOn_artanh` as
  companions, and `HasDerivAt.artanh` as the chain-rule form.
* `Real.tendsto_artanh_div_nhdsNE_zero` — `artanh t / t` tends to `1` as `t` tends to
  `0` through nonzero values: the derivative at the origin, read as a limit of slopes. This is
  what turns a closed-form hyperbolic distance into an infinitesimal one.
* `Real.integral_one_sub_sq_inv_eq_artanh` — `artanh` is the primitive of the density
  `(1 - t ^ 2)⁻¹`: `∫ t in (0)..r, (1 - t ^ 2)⁻¹ = artanh r` for `r ∈ (-1, 1)`.
* `Real.self_le_artanh` and `Real.artanh_le_self_div_one_sub_sq` — the two-sided comparison
  `x ≤ artanh x ≤ x / (1 - x ^ 2)` on `[0, 1)`, obtained by bounding that integrand between
  its values at the two endpoints.

The motivation is the conformal-mapping roadmap (`TauCetiRoadmap/ConformalMapping/README.md`),
whose layer L2 asks for the hyperbolic (Poincaré) metric on the unit disc. Tau Ceti's
`TauCeti.hyperbolicDist` is `Real.artanh` of the pseudo-hyperbolic expression, so its
infinitesimal form — proved in `TauCeti/Analysis/Complex/Conformal/Hyperbolic/Density.lean` —
is exactly the derivative of `Real.artanh` at the origin transported along that expression.
Nothing here is complex-analytic, so it is stated for `Real.artanh` alone, at the natural
generality of a real special function, rather than being buried in the disc files.
-/

public section

namespace TauCeti

open Set

open scoped Topology

/-! ### Differentiability -/

/-- **The derivative of the inverse hyperbolic tangent.** On the interval `(-1, 1)` where
`Real.artanh` inverts `Real.tanh`, it has derivative `(1 - x ^ 2)⁻¹`.

Mathlib records no differentiability statement for `Real.artanh`; this is proved from the
logarithmic formula `Real.artanh_eq_half_log`, which holds on all of `(-1, 1)` and hence on a
neighbourhood of each of its points. -/
theorem _root_.Real.hasDerivAt_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 - x ^ 2)⁻¹ x := by
  have hx₁ : (-1 : ℝ) < x := hx.1
  have hx₂ : x < 1 := hx.2
  have hsub : (1 : ℝ) - x ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hadd : (1 : ℝ) + x ≠ 0 := by intro h; linarith [add_eq_zero_iff_eq_neg.mp h]
  have hpos : (0 : ℝ) < (1 + x) / (1 - x) := div_pos (by linarith) (by linarith)
  have hnum : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have hden : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hquot : HasDerivAt (fun y : ℝ => (1 + y) / (1 - y))
      ((1 * (1 - x) - (1 + x) * -1) / (1 - x) ^ 2) x := hnum.div hden hsub
  have hlog : HasDerivAt (fun y : ℝ => Real.log ((1 + y) / (1 - y)))
      ((1 * (1 - x) - (1 + x) * -1) / (1 - x) ^ 2 / ((1 + x) / (1 - x))) x :=
    hquot.log hpos.ne'
  have hfactor : (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) := by ring
  have hval : 1 / 2 * ((1 * (1 - x) - (1 + x) * -1) / (1 - x) ^ 2 / ((1 + x) / (1 - x)))
      = (1 - x ^ 2)⁻¹ := by
    rw [hfactor]
    field_simp
    ring
  have hhalf : HasDerivAt (fun y : ℝ => 1 / 2 * Real.log ((1 + y) / (1 - y)))
      (1 - x ^ 2)⁻¹ x := hval ▸ hlog.const_mul (1 / 2 : ℝ)
  refine hhalf.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact Real.artanh_eq_half_log (Ioo_subset_Icc_self hy)

/-- `Real.artanh` is differentiable at each point of `(-1, 1)`. -/
theorem _root_.Real.differentiableAt_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ Real.artanh x :=
  (Real.hasDerivAt_artanh hx).differentiableAt

/-- The derivative of `Real.artanh` on `(-1, 1)`, in `deriv` form. -/
theorem _root_.Real.deriv_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    deriv Real.artanh x = (1 - x ^ 2)⁻¹ :=
  (Real.hasDerivAt_artanh hx).deriv

/-- `Real.artanh` is differentiable on `(-1, 1)`. -/
theorem _root_.Real.differentiableOn_artanh :
    DifferentiableOn ℝ Real.artanh (Ioo (-1 : ℝ) 1) := fun _ hx =>
  (Real.differentiableAt_artanh hx).differentiableWithinAt

/-- `Real.artanh` is continuous at each point of `(-1, 1)`. -/
theorem _root_.Real.continuousAt_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt Real.artanh x :=
  (Real.differentiableAt_artanh hx).continuousAt

/-- `Real.artanh` is continuous on the interval `(-1, 1)` on which it inverts `Real.tanh`. -/
theorem _root_.Real.continuousOn_artanh : ContinuousOn Real.artanh (Ioo (-1 : ℝ) 1) := fun _ hx =>
  (Real.continuousAt_artanh hx).continuousWithinAt

/-- The chain rule for `Real.artanh`: composing with a function that is differentiable at `x`
and takes a value in `(-1, 1)` there multiplies the derivative by `(1 - f x ^ 2)⁻¹`. -/
theorem _root_.HasDerivAt.artanh {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (hx : f x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y => Real.artanh (f y)) ((1 - f x ^ 2)⁻¹ * f') x :=
  (Real.hasDerivAt_artanh hx).comp x hf

/-! ### The derivative at the origin, as a limit of slopes -/

/-- **The infinitesimal form of `Real.artanh` at the origin.** Since `artanh 0 = 0` and the
derivative of `Real.artanh` at `0` is `1`, the quotient `artanh t / t` tends to `1` as `t`
tends to `0` through nonzero values.

This is the one-variable input to the infinitesimal Poincaré density: on the unit disc the
hyperbolic distance is `Real.artanh` of the pseudo-hyperbolic expression, and near the diagonal
the latter is small, so this limit converts the closed form into a density. -/
theorem _root_.Real.tendsto_artanh_div_nhdsNE_zero :
    Filter.Tendsto (fun t : ℝ => Real.artanh t / t) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have h : Filter.Tendsto (slope Real.artanh 0) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa using (Real.hasDerivAt_artanh (x := (0 : ℝ)) (by norm_num)).tendsto_slope
  refine Filter.Tendsto.congr (fun t => ?_) h
  rw [slope_def_field, Real.artanh_zero, sub_zero, sub_zero]

/-! ### `Real.artanh` as the primitive of the Poincaré density -/

/-- On any closed interval inside `(-1, 1)` the Poincaré density `(1 - t ^ 2)⁻¹` is
continuous, since its denominator does not vanish there. -/
private lemma continuousOn_one_sub_sq_inv {s : Set ℝ} (hs : s ⊆ Ioo (-1 : ℝ) 1) :
    ContinuousOn (fun t : ℝ => (1 - t ^ 2)⁻¹) s := by
  refine ContinuousOn.inv₀ (by fun_prop) fun t ht => ?_
  obtain ⟨ht₁, ht₂⟩ := hs ht
  have : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  exact this.ne'

/-- **`Real.artanh` is the primitive of `(1 - t ^ 2)⁻¹`.** For `r` in `(-1, 1)`,
`∫ t in (0)..r, (1 - t ^ 2)⁻¹ = artanh r`.

On the unit disc this says that the hyperbolic distance from the origin out to a point at
Euclidean radius `r` is the length of that radius measured in the Poincaré density
`|dz| / (1 - |z| ^ 2)`. -/
theorem _root_.Real.integral_one_sub_sq_inv_eq_artanh {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    (∫ t in (0 : ℝ)..r, (1 - t ^ 2)⁻¹) = Real.artanh r := by
  have hsub : uIcc (0 : ℝ) r ⊆ Ioo (-1 : ℝ) 1 :=
    Set.ordConnected_Ioo.uIcc_subset (by norm_num) hr
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := Real.artanh) (f' := fun t : ℝ => (1 - t ^ 2)⁻¹)
    (fun t ht => Real.hasDerivAt_artanh (hsub ht))
    (continuousOn_one_sub_sq_inv hsub).intervalIntegrable
  rw [hFTC, Real.artanh_zero, sub_zero]

/-- **The elementary lower bound `x ≤ artanh x` on `[0, 1)`**: the Poincaré density
`(1 - t ^ 2)⁻¹` is at least `1`, so the hyperbolic distance dominates the Euclidean one. -/
theorem _root_.Real.self_le_artanh {x : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1) : x ≤ Real.artanh x := by
  have hmem : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hx₁⟩
  have hsub : uIcc (0 : ℝ) x ⊆ Ioo (-1 : ℝ) 1 :=
    Set.ordConnected_Ioo.uIcc_subset (by norm_num) hmem
  rw [← Real.integral_one_sub_sq_inv_eq_artanh hmem]
  calc x = ∫ _t in (0 : ℝ)..x, (1 : ℝ) := by simp
    _ ≤ ∫ t in (0 : ℝ)..x, (1 - t ^ 2)⁻¹ := by
        refine intervalIntegral.integral_mono_on hx intervalIntegrable_const
          (continuousOn_one_sub_sq_inv hsub).intervalIntegrable fun t ht => ?_
        have ht₂ : t < 1 := lt_of_le_of_lt ht.2 hx₁
        have hpos : (0 : ℝ) < 1 - t ^ 2 := by nlinarith [ht.1]
        exact (one_le_inv₀ hpos).2 (by nlinarith [ht.1])

/-- **The elementary upper bound `artanh x ≤ x / (1 - x ^ 2)` on `[0, 1)`**: the Poincaré
density `(1 - t ^ 2)⁻¹` is increasing, so on `[0, x]` it is at most its value at `x`. -/
theorem _root_.Real.artanh_le_self_div_one_sub_sq {x : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1) :
    Real.artanh x ≤ x / (1 - x ^ 2) := by
  have hmem : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hx₁⟩
  have hxpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
  have hsub : uIcc (0 : ℝ) x ⊆ Ioo (-1 : ℝ) 1 :=
    Set.ordConnected_Ioo.uIcc_subset (by norm_num) hmem
  rw [← Real.integral_one_sub_sq_inv_eq_artanh hmem]
  calc (∫ t in (0 : ℝ)..x, (1 - t ^ 2)⁻¹) ≤ ∫ _t in (0 : ℝ)..x, (1 - x ^ 2)⁻¹ := by
        refine intervalIntegral.integral_mono_on hx
          (continuousOn_one_sub_sq_inv hsub).intervalIntegrable intervalIntegrable_const
          fun t ht => ?_
        exact inv_anti₀ hxpos (by nlinarith [ht.1, ht.2])
    _ = x / (1 - x ^ 2) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, div_eq_mul_inv]

end TauCeti
