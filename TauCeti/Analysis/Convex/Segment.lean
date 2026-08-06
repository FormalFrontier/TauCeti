/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.Ray

/-!
# Membership in a segment with an endpoint at the origin

Mathlib describes membership in a segment through the ray predicate `SameRay` by
`mem_segment_iff_sameRay`: `x ∈ [y -[𝕜] z] ↔ SameRay 𝕜 (x - y) (z - x)`. That form is symmetric in
the two endpoints, and the differences `x - y`, `z - x` are exactly what a *metric* consumer does
not want: such a consumer holds a point `m` and an endpoint `w`, and asks whether `m` lies on the
segment `[0, w]` in terms of the two data it can measure — the direction of `m` against `w`, and
the two norms. This file supplies that reading, together with its mirror in which the origin sits
in the *middle* of the segment rather than at an end, and the inner-product form of both.

Each criterion is stated at the generality its proof uses. The origin-in-the-middle one needs no
norm at all, and is stated for a module over a linearly ordered field; the origin-at-an-end one
compares two norms, and is stated for a real normed space; the inner-product forms replace
`SameRay` by the equality case of the Cauchy--Schwarz inequality, and are stated for a real inner
product space.

The bridge between the ray forms and the inner-product forms is
`TauCeti.sameRay_iff_real_inner_eq_norm_mul`: two vectors of a real inner product space lie on a
common ray exactly when Cauchy--Schwarz is an equality for them. Mathlib has both halves of it —
`inner_eq_norm_mul_iff_real : ⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y` and
`sameRay_iff_norm_smul_eq : SameRay ℝ x y ↔ ‖x‖ • y = ‖y‖ • x` — but not the composite, which is
what makes the geometric content visible. No strict convexity is involved: the alternative route
through `sameRay_iff_norm_add` would need a `StrictConvexSpace ℝ E` instance, whereas
`sameRay_iff_norm_smul_eq` and `inner_eq_norm_mul_iff_real` hold in any normed, respectively inner
product, space.

## Main results

* `TauCeti.zero_mem_segment_iff_sameRay_neg` — `0 ∈ [x -[𝕜] y] ↔ SameRay 𝕜 x (-y)`.
* `TauCeti.mem_segment_zero_left_iff_sameRay` —
  `m ∈ [0 -[ℝ] w] ↔ SameRay ℝ m w ∧ ‖m‖ ≤ ‖w‖`. Both conjuncts are needed.
* `TauCeti.eq_of_mem_segment_zero_left_of_norm_eq` — the norm separates the points of `[0, w]`.
* `TauCeti.sameRay_iff_real_inner_eq_norm_mul` — the ray predicate as the equality case of
  Cauchy--Schwarz.
* `TauCeti.mem_segment_zero_left_iff_real_inner_eq_norm_mul` and
  `TauCeti.zero_mem_segment_iff_real_inner_eq_neg_norm_mul` — the two criteria in a real inner
  product space.

The consumer is `TauCeti/Analysis/Complex/Conformal/Poincare/Betweenness.lean`, which identifies
the hyperbolic segments of the Poincaré disc issuing from, or straddling, the origin with the
Euclidean ones; `ℂ` is a real inner product space with `⟪w, z⟫_ℝ = (z * conj w).re`
(`Complex.inner`), so the two inner-product criteria are what that file needs. It proved them
itself, by hand, in the complex-number-specific `Complex.normSq` language and only for `ℂ`, its
own docstrings recording that they are "statements about complex numbers rather than about the
hyperbolic metric". Nothing in them is about complex numbers either, which is why they live here.
This supports the hyperbolic-metric layer L2 of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`) without adding to it.
-/

public section

namespace TauCeti

open RealInnerProductSpace Set
open scoped Convex

/-! ### Segments and rays -/

section Module

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] {x y : E}

/-- **The origin lies between two points exactly when they point in opposite directions.** This is
`mem_segment_iff_sameRay` evaluated at the point `0`, with the resulting `SameRay 𝕜 (-x) y`
rewritten by `sameRay_neg_swap`.

No nondegeneracy is needed: if `x = 0` then `0` is an endpoint of the segment and `SameRay 𝕜 0 (-y)`
holds, and symmetrically for `y`. -/
theorem zero_mem_segment_iff_sameRay_neg : (0 : E) ∈ [x -[𝕜] y] ↔ SameRay 𝕜 x (-y) := by
  rw [mem_segment_iff_sameRay, zero_sub, sub_zero, sameRay_neg_swap]

end Module

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m w : E}

/-- **Membership in the segment from the origin, read off the direction and the two norms.** A
point `m` lies on `[0, w]` exactly when it points along `w` and is no further from the origin than
`w` is.

Both conjuncts are needed: for `w ≠ 0` the point `(2 : ℝ) • w` satisfies the first without
satisfying the second. -/
theorem mem_segment_zero_left_iff_sameRay :
    m ∈ [(0 : E) -[ℝ] w] ↔ SameRay ℝ m w ∧ ‖m‖ ≤ ‖w‖ := by
  rw [segment_eq_image' ℝ (0 : E) w]
  simp only [mem_image, mem_Icc, zero_add, sub_zero]
  constructor
  · rintro ⟨t, ⟨ht₀, ht₁⟩, rfl⟩
    refine ⟨SameRay.sameRay_nonneg_smul_left w ht₀, ?_⟩
    rw [norm_smul, Real.norm_of_nonneg ht₀]
    nlinarith [norm_nonneg w]
  · rintro ⟨hray, hle⟩
    rcases eq_or_ne w 0 with rfl | hw
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      simpa using (norm_le_zero_iff.mp (by simpa using hle)).symm
    -- With `w ≠ 0` the ray condition `‖m‖ • w = ‖w‖ • m` solves for `m` as `(‖m‖ / ‖w‖) • w`,
    -- and the norm comparison places that scalar in `[0, 1]`.
    · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      refine ⟨‖m‖ / ‖w‖, ⟨by positivity, (div_le_one hwpos).mpr hle⟩, ?_⟩
      rw [div_eq_inv_mul, mul_smul, hray.norm_smul_eq, inv_smul_smul₀ hwpos.ne']

/-- **Two points of a segment from the origin with the same norm coincide.** The segment `[0, w]`
carries no two distinct points at the same distance from `0`: it is contained in a ray, on which
the norm is injective (`norm_injOn_ray_right`). -/
theorem eq_of_mem_segment_zero_left_of_norm_eq {m₁ m₂ : E} (h₁ : m₁ ∈ [(0 : E) -[ℝ] w])
    (h₂ : m₂ ∈ [(0 : E) -[ℝ] w]) (h : ‖m₁‖ = ‖m₂‖) : m₁ = m₂ := by
  rcases eq_or_ne w 0 with rfl | hw
  · rw [segment_same, mem_singleton_iff] at h₁ h₂
    rw [h₁, h₂]
  · exact norm_injOn_ray_right hw (mem_segment_zero_left_iff_sameRay.mp h₁).1
      (mem_segment_zero_left_iff_sameRay.mp h₂).1 h

end Normed

/-! ### The inner-product forms -/

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {x y : F}

/-- **Two vectors lie on a common ray exactly when Cauchy–Schwarz is an equality for them.** Both
sides are Mathlib's, in the shapes `sameRay_iff_norm_smul_eq` and `inner_eq_norm_mul_iff_real`
give them; only the composite is new. -/
theorem sameRay_iff_real_inner_eq_norm_mul : SameRay ℝ x y ↔ ⟪x, y⟫ = ‖x‖ * ‖y‖ := by
  rw [sameRay_iff_norm_smul_eq, inner_eq_norm_mul_iff_real, eq_comm]

/-- **Membership in the segment from the origin, read off the inner product.** The inner-product
form of `TauCeti.mem_segment_zero_left_iff_sameRay`. -/
theorem mem_segment_zero_left_iff_real_inner_eq_norm_mul :
    x ∈ [(0 : F) -[ℝ] y] ↔ ⟪x, y⟫ = ‖x‖ * ‖y‖ ∧ ‖x‖ ≤ ‖y‖ := by
  rw [mem_segment_zero_left_iff_sameRay, sameRay_iff_real_inner_eq_norm_mul]

/-- **The origin lies between two vectors exactly when their inner product is minimal.** The
inner-product form of `TauCeti.zero_mem_segment_iff_sameRay_neg`: Cauchy–Schwarz is an equality at
the other end of its range, `⟪x, y⟫_ℝ = -(‖x‖ * ‖y‖)`. -/
theorem zero_mem_segment_iff_real_inner_eq_neg_norm_mul :
    (0 : F) ∈ [x -[ℝ] y] ↔ ⟪x, y⟫ = -(‖x‖ * ‖y‖) := by
  rw [zero_mem_segment_iff_sameRay_neg, sameRay_iff_real_inner_eq_norm_mul, inner_neg_right,
    norm_neg, neg_eq_iff_eq_neg]

end InnerProduct

end TauCeti
