/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.InnerProductSpace.Parseval
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.HilbertBasis

/-!
# Parseval and coordinates for the Hermite basis of `L²(ℝ)`

`TauCeti.hermiteHilbertBasis` exhibits the Hermite functions as a Hilbert basis of `L²(ℝ; 𝕜)`.
This file states the expansion identities that basis was built for, phrased in terms of the
explicit vectors `TauCeti.hermiteFunctionLp` rather than the bundled basis, so that a consumer
never has to unfold `hermiteHilbertBasis` to expand a function in Hermite functions.

## Main statements

* `TauCeti.hermiteHilbertBasis_repr_apply` — the `n`-th coordinate of `f` is `⟪ψₙ, f⟫`.
* `TauCeti.tsum_inner_mul_inner_hermiteFunctionLp` — Parseval in polarized form,
  `∑' n, ⟪f, ψₙ⟫ * ⟪ψₙ, g⟫ = ⟪f, g⟫`.
* `TauCeti.tsum_norm_sq_inner_hermiteFunctionLp` — Parseval in norm-square form,
  `∑' n, ‖⟪ψₙ, f⟫‖² = ‖f‖²`.
* `TauCeti.hermiteHilbertBasis_repr_self` — the coordinates of a basis vector are a single `1`.
* `TauCeti.hasSum_hermiteFunctionLp_expansion` — the Hermite expansion `∑' n, ⟪ψₙ, f⟫ • ψₙ = f`.

Every statement holds for an arbitrary `RCLike` scalar field, so `𝕜 = ℝ` and `𝕜 = ℂ` are the same
theorem. The roadmap `OrthogonalL2Bases` Part A3 acceptance criteria on the coordinates and norm
of `ψ₀` follow by instantiating `hermiteHilbertBasis_repr_self` and
`tsum_norm_sq_inner_hermiteFunctionLp` at `f = ψ₀`, together with `norm_hermiteFunctionLp 0`;
no separate declaration is needed for that specialization.
-/

public section

namespace TauCeti

open MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The coordinates of `f` in the Hermite basis are its inner products against the Hermite
functions. -/
@[simp]
theorem hermiteHilbertBasis_repr_apply (f : Lp 𝕜 2 (volume : Measure ℝ)) (n : ℕ) :
    (hermiteHilbertBasis 𝕜).repr f n = inner 𝕜 (hermiteFunctionLp 𝕜 n) f := by
  simpa using (hermiteHilbertBasis 𝕜).repr_apply_apply f n

/-- **Parseval's identity for the Hermite basis** (polarized form): the Hermite coordinates of
`f` and `g` pair to their inner product. -/
theorem tsum_inner_mul_inner_hermiteFunctionLp (f g : Lp 𝕜 2 (volume : Measure ℝ)) :
    ∑' n : ℕ, inner 𝕜 f (hermiteFunctionLp 𝕜 n) * inner 𝕜 (hermiteFunctionLp 𝕜 n) g
      = inner 𝕜 f g := by
  simpa using (hermiteHilbertBasis 𝕜).tsum_inner_mul_inner f g

/-- **Parseval's identity for the Hermite basis** (norm-square form): the squared Hermite
coordinates of `f` sum to `‖f‖²`. This is the roadmap's Part A3 acceptance criterion. -/
theorem tsum_norm_sq_inner_hermiteFunctionLp (f : Lp 𝕜 2 (volume : Measure ℝ)) :
    ∑' n : ℕ, ‖inner 𝕜 (hermiteFunctionLp 𝕜 n) f‖ ^ 2 = ‖f‖ ^ 2 := by
  simpa using (hermiteHilbertBasis 𝕜).tsum_norm_sq_inner f

/-- The squared Hermite coordinate family of an `L²` function is summable. -/
theorem summable_norm_sq_inner_hermiteFunctionLp (f : Lp 𝕜 2 (volume : Measure ℝ)) :
    Summable fun n : ℕ => ‖inner 𝕜 (hermiteFunctionLp 𝕜 n) f‖ ^ 2 := by
  simpa using (hermiteHilbertBasis 𝕜).summable_norm_sq_inner f

/-- **The Hermite expansion.** Every `f ∈ L²(ℝ)` is the sum of its Hermite series. -/
theorem hasSum_hermiteFunctionLp_expansion (f : Lp 𝕜 2 (volume : Measure ℝ)) :
    HasSum (fun n : ℕ => inner 𝕜 (hermiteFunctionLp 𝕜 n) f • hermiteFunctionLp 𝕜 n) f := by
  simpa [hermiteHilbertBasis_repr_apply] using (hermiteHilbertBasis 𝕜).hasSum_repr f

/-- The coordinates of the `n`-th Hermite function are a single `1` in position `n`. -/
@[simp]
theorem hermiteHilbertBasis_repr_self (n : ℕ) :
    (hermiteHilbertBasis 𝕜).repr (hermiteFunctionLp 𝕜 n) = lp.single 2 n (1 : 𝕜) := by
  classical
  simpa using (hermiteHilbertBasis 𝕜).repr_self n

end TauCeti
