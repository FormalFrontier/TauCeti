/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Parseval's identity in norm-square form

Mathlib's `HilbertBasis.hasSum_inner_mul_inner` gives the polarized Parseval identity
`∑' i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫`, valued in the scalar field `𝕜`. The diagonal case `y = x`
of that identity is the familiar real-valued statement `‖x‖² = ∑' i, ‖⟪b i, x⟫‖²`, but it is not
a substitution instance: the summands `⟪x, b i⟫ * ⟪b i, x⟫` are `𝕜`-valued, and turning them into
the real numbers `‖⟪b i, x⟫‖²` uses `RCLike.conj_mul` termwise and descends the sum along
`RCLike.hasSum_ofReal`. This file performs that descent once.

The real-valued form is the shape consumers state coefficient decay in, and it is the
`OrthogonalL2Bases` roadmap's Part A3 acceptance criterion `‖f‖² = ∑' n, ‖⟪ψₙ, f⟫‖²`; its instance
for the Hermite basis is `TauCeti.tsum_norm_sq_inner_hermiteFunctionLp`.
-/

public section

namespace TauCeti

variable {ι : Type*} {𝕜 : Type*} {E : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Parseval's identity, norm-square form.** The squared coordinates of `x` in a Hilbert basis
sum to `‖x‖²`, as a convergent series of real numbers. This is the `repr` isometry
`b.repr : E ≃ₗᵢ[𝕜] ℓ²(ι, 𝕜)` transported along `lp.hasSum_norm`, the norm-summability already
proved for `ℓ²`. -/
theorem _root_.HilbertBasis.hasSum_norm_sq_inner (b : _root_.HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => ‖inner 𝕜 (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply, b.repr.norm_map] using h

/-- **Parseval's identity, norm-square form** (`tsum` version of
`HilbertBasis.hasSum_norm_sq_inner`). -/
theorem _root_.HilbertBasis.tsum_norm_sq_inner (b : _root_.HilbertBasis ι 𝕜 E) (x : E) :
    ∑' i : ι, ‖inner 𝕜 (b i) x‖ ^ 2 = ‖x‖ ^ 2 :=
  (b.hasSum_norm_sq_inner x).tsum_eq

/-- The squared coordinate family of a vector is summable. -/
theorem _root_.HilbertBasis.summable_norm_sq_inner (b : _root_.HilbertBasis ι 𝕜 E) (x : E) :
    Summable fun i => ‖inner 𝕜 (b i) x‖ ^ 2 :=
  (b.hasSum_norm_sq_inner x).summable

end TauCeti
