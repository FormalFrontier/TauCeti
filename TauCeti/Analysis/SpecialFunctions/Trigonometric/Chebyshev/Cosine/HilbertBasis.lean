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
* `TauCeti.chebyshevCosineL2Equiv_normalizedChebyshevTLp` identifies the transported normalized
  Chebyshev modes.
* `TauCeti.chebyshevCosineHilbertBasis_repr_chebyshevCosineL2Equiv` identifies coordinates across
  the cosine equivalence.
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

/-! ## Transfer across the cosine change of variables -/

/-- **The cosine change of variables carries Chebyshev polynomial modes to cosine modes.**
`chebyshevCosineL2Equiv` maps the normalized Chebyshev mode `Tₙ / √cₙ` in `L²(measureT)` to the
normalized angular cosine mode `cos (nθ) / √cₙ` in `L²(chebyshevAngleMeasure)`. -/
@[simp]
theorem chebyshevCosineL2Equiv_normalizedChebyshevTLp (n : ℕ) :
    chebyshevCosineL2Equiv 𝕜 (normalizedChebyshevTLp 𝕜 n) =
      chebyshevCosineHilbertBasis 𝕜 n := by
  rw [chebyshevCosineHilbertBasis, HilbertBasis.mapₗᵢ_apply, coe_chebyshevTHilbertBasis]

/-- The inverse cosine equivalence maps the normalized cosine mode back to the normalized Chebyshev
polynomial mode. -/
@[simp]
theorem chebyshevCosineL2Equiv_symm_chebyshevCosineHilbertBasis (n : ℕ) :
    (chebyshevCosineL2Equiv 𝕜).symm (chebyshevCosineHilbertBasis 𝕜 n) =
      normalizedChebyshevTLp 𝕜 n := by
  rw [← chebyshevCosineL2Equiv_normalizedChebyshevTLp, LinearIsometryEquiv.symm_apply_apply]

/-- **Coordinates are preserved under the cosine change of variables.** The `n`-th coordinate of
`f ∘ cos` in the Chebyshev cosine basis equals the `n`-th coordinate of `f` in the Chebyshev
polynomial basis. -/
@[simp]
theorem chebyshevCosineHilbertBasis_repr_chebyshevCosineL2Equiv
    (g : Lp 𝕜 2 (measureT : Measure ℝ)) (n : ℕ) :
    (chebyshevCosineHilbertBasis 𝕜).repr (chebyshevCosineL2Equiv 𝕜 g) n =
      (chebyshevTHilbertBasis 𝕜).repr g n := by
  rw [(chebyshevCosineHilbertBasis 𝕜).repr_apply_apply,
    (chebyshevTHilbertBasis 𝕜).repr_apply_apply,
    ← chebyshevCosineL2Equiv_normalizedChebyshevTLp, coe_chebyshevTHilbertBasis,
    LinearIsometryEquiv.inner_map_map]

/-- The inverse coordinate identification: the Chebyshev polynomial coordinate of `f ∘ arccos`
equals the cosine coordinate of `f`. -/
@[simp]
theorem chebyshevTHilbertBasis_repr_chebyshevCosineL2Equiv_symm
    (f : Lp 𝕜 2 chebyshevAngleMeasure) (n : ℕ) :
    (chebyshevTHilbertBasis 𝕜).repr ((chebyshevCosineL2Equiv 𝕜).symm f) n =
      (chebyshevCosineHilbertBasis 𝕜).repr f n := by
  rw [← chebyshevCosineHilbertBasis_repr_chebyshevCosineL2Equiv,
    LinearIsometryEquiv.apply_symm_apply]

/-- Pairing against the normalized cosine mode in `L²(chebyshevAngleMeasure)` is pairing against
the normalized Chebyshev polynomial mode in `L²(measureT)`. -/
@[simp]
theorem inner_chebyshevCosineHilbertBasis_chebyshevCosineL2Equiv
    (n : ℕ) (g : Lp 𝕜 2 (measureT : Measure ℝ)) :
    inner 𝕜 (chebyshevCosineHilbertBasis 𝕜 n) (chebyshevCosineL2Equiv 𝕜 g) =
      inner 𝕜 (normalizedChebyshevTLp 𝕜 n) g := by
  rw [← chebyshevCosineL2Equiv_normalizedChebyshevTLp, LinearIsometryEquiv.inner_map_map]

end L2

end TauCeti
