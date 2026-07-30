/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasisMap
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Cosine.Transfer
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.HilbertBasis

/-!
# The Chebyshev basis as a cosine basis

Transporting `TauCeti.chebyshevTHilbertBasis` across `TauCeti.chebyshevCosineL2Equiv` gives a
Hilbert basis on the angular interval. Its `n`th vector is the normalized cosine
`cos (nθ) / √cₙ`, where `c₀ = π` and `cₙ = π / 2` for `n > 0`. This is the unitary-transfer
statement required by Part C of the `OrthogonalL2Bases` roadmap.

## Main declarations

* `TauCeti.chebyshevCosineHilbertBasis` is the transported Chebyshev basis.
* `TauCeti.coeFn_chebyshevCosineHilbertBasis` identifies its vectors with the normalized cosines.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

section L2

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The normalized cosine Hilbert basis of `L²((0, π])`, obtained by transporting the normalized
Chebyshev `T` basis under `x = cos θ`. -/
noncomputable def chebyshevCosineHilbertBasis :
    HilbertBasis ℕ 𝕜 (Lp 𝕜 2 chebyshevAngleMeasure) :=
  (chebyshevTHilbertBasis 𝕜).mapₗᵢ (chebyshevCosineL2Equiv 𝕜)

/-- **Chebyshev-cosine basis correspondence.** The `n`th vector of the transported Chebyshev basis
is almost everywhere the scalar-cast normalized cosine `cos (nθ) / √cₙ`. -/
theorem coeFn_chebyshevCosineHilbertBasis (n : ℕ) :
    ⇑(chebyshevCosineHilbertBasis 𝕜 n) =ᵐ[chebyshevAngleMeasure]
      fun θ => (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) := by
  rw [chebyshevCosineHilbertBasis, HilbertBasis.mapₗᵢ_apply]
  filter_upwards [
    chebyshevCosineL2Equiv_apply 𝕜 (chebyshevTHilbertBasis 𝕜 n),
    measurePreserving_cos_chebyshev.quasiMeasurePreserving.ae_eq
      (coeFn_normalizedChebyshevTLp (𝕜 := 𝕜) n)] with θ hcos hmode
  rw [hcos, coe_chebyshevTHilbertBasis]
  exact hmode.trans (congrArg (algebraMap ℝ 𝕜) (by
    rw [normalizedChebyshevT_def, normalized_eval_T_real_cos_eq_normalizedChebyshevCosine]))

end L2

end TauCeti
