/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.Parseval
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.HilbertBasis

/-!
# Parseval and expansions for the Chebyshev basis

`TauCeti.chebyshevTHilbertBasis` identifies the normalized Chebyshev `T` polynomials as a
Hilbert basis of `L²(Polynomial.Chebyshev.measureT; 𝕜)`. This file exports the resulting
coordinates, Parseval identities, and series expansion using the explicit vectors
`TauCeti.normalizedChebyshevTLp`.

These statements make the Part C basis from the `OrthogonalL2Bases` roadmap directly usable:
consumers can compute Chebyshev coefficients and reconstruct a function without unfolding the
bundled Hilbert basis. They hold uniformly for every `RCLike` scalar field.

## Main statements

* `TauCeti.chebyshevTHilbertBasis_repr_apply` identifies each coordinate with an inner product.
* `TauCeti.tsum_inner_mul_inner_normalizedChebyshevTLp` is polarized Parseval.
* `TauCeti.tsum_norm_sq_inner_normalizedChebyshevTLp` is norm-square Parseval.
* `TauCeti.hasSum_normalizedChebyshevTLp_expansion` reconstructs every `L²` vector.
* `TauCeti.chebyshevTHilbertBasis_repr_self` computes the coordinates of a basis vector.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The `n`-th Chebyshev coordinate of `f` is its inner product against the normalized `Tₙ`. -/
@[simp]
theorem chebyshevTHilbertBasis_repr_apply (f : Lp 𝕜 2 measureT) (n : ℕ) :
    (chebyshevTHilbertBasis 𝕜).repr f n = inner 𝕜 (normalizedChebyshevTLp 𝕜 n) f := by
  simpa using (chebyshevTHilbertBasis 𝕜).repr_apply_apply f n

/-- **Parseval's identity for the Chebyshev basis** (polarized form). -/
theorem tsum_inner_mul_inner_normalizedChebyshevTLp (f g : Lp 𝕜 2 measureT) :
    ∑' n : ℕ, inner 𝕜 f (normalizedChebyshevTLp 𝕜 n) *
        inner 𝕜 (normalizedChebyshevTLp 𝕜 n) g = inner 𝕜 f g := by
  simpa using (chebyshevTHilbertBasis 𝕜).tsum_inner_mul_inner f g

/-- **Parseval's identity for the Chebyshev basis** (norm-square form): the squared Chebyshev
coefficients of `f` sum to `‖f‖²`. -/
theorem tsum_norm_sq_inner_normalizedChebyshevTLp (f : Lp 𝕜 2 measureT) :
    ∑' n : ℕ, ‖inner 𝕜 (normalizedChebyshevTLp 𝕜 n) f‖ ^ 2 = ‖f‖ ^ 2 := by
  simpa using (chebyshevTHilbertBasis 𝕜).tsum_norm_sq_inner f

/-- The squared Chebyshev coefficient family of an `L²` function is summable. -/
theorem summable_norm_sq_inner_normalizedChebyshevTLp (f : Lp 𝕜 2 measureT) :
    Summable fun n : ℕ => ‖inner 𝕜 (normalizedChebyshevTLp 𝕜 n) f‖ ^ 2 := by
  simpa using (chebyshevTHilbertBasis 𝕜).summable_norm_sq_inner f

/-- **The Fourier–Chebyshev expansion.** Every vector in `L²(measureT)` is the sum of its
normalized Chebyshev series. -/
theorem hasSum_normalizedChebyshevTLp_expansion (f : Lp 𝕜 2 measureT) :
    HasSum
      (fun n : ℕ =>
        inner 𝕜 (normalizedChebyshevTLp 𝕜 n) f • normalizedChebyshevTLp 𝕜 n)
      f := by
  simpa [chebyshevTHilbertBasis_repr_apply] using (chebyshevTHilbertBasis 𝕜).hasSum_repr f

/-- The coordinates of the `n`-th normalized Chebyshev mode are a single `1` in position `n`. -/
@[simp]
theorem chebyshevTHilbertBasis_repr_self (n : ℕ) :
    (chebyshevTHilbertBasis 𝕜).repr (normalizedChebyshevTLp 𝕜 n) =
      lp.single 2 n (1 : 𝕜) := by
  classical
  simpa using (chebyshevTHilbertBasis 𝕜).repr_self n

end TauCeti
