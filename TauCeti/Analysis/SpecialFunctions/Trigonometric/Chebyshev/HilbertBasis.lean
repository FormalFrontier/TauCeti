module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Span
public import TauCeti.Probability.Moments.VanishingMoments

/-!
# The Chebyshev `T` polynomials as a Hilbert basis of `L²(measureT)`

Roadmap **Part C**: the normalized Chebyshev `T` modes `Tₙ/√‖Tₙ‖²` are a Hilbert basis of
`L²([-1,1]; measureT)`, where `measureT` is Mathlib's Chebyshev orthogonality measure (weight
`(1-x²)^{-1/2}`).

Every input is already merged; this file only supplies the missing assembly. Orthonormality is
`TauCeti.orthonormal_normalizedChebyshevTLp`; completeness is the one step that had been left open,
because it needs the **function-level** moment-determinacy theorem
`TauCeti.ae_eq_zero_of_forall_moment_eq_zero_of_finite_expMoments` (a vector of `L²(measureT)`
orthogonal to every monomial is a.e. `0`), whose exponential-moment hypothesis is free here: the
Chebyshev measure has compact support `[-1,1]`, so `e^{|x|}` is integrable against it.

The bridge from mode-orthogonality to monomial-orthogonality is
`TauCeti.inner_polynomialEvalChebyshevLp_eq_zero`.

## Main statements

* `TauCeti.chebyshevTHilbertBasis` — the Chebyshev `T` Hilbert basis of `L²(measureT)`.
* `TauCeti.coe_chebyshevTHilbertBasis` — the anti-vacuity pin: the `n`-th basis vector is the
  normalized mode `Tₙ/√‖Tₙ‖²`.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Polynomial.Chebyshev

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The Chebyshev measure has a finite exponential moment: `e^{|x|}` is integrable against
`measureT`, immediate from compact support `[-1,1]` (there `|x| ≤ 1`, so the integrand is bounded)
and finiteness of `measureT`. This is the hypothesis the completeness engine consumes. -/
theorem exp_moment_measureT :
    ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|)) measureT :=
  ⟨1, one_pos,
    integrable_measureT (by fun_prop : ContinuousOn (fun x : ℝ => Real.exp (1 * |x|))
      (Set.Icc (-1) 1))⟩

/-- **Monomial-orthogonality from mode-orthogonality.** A vector of `L²(measureT)` orthogonal to
every normalized Chebyshev mode has every scalar-cast monomial moment `∫ (x : 𝕜)ⁿ · g` vanishing.
This threads `inner_polynomialEvalChebyshevLp_eq_zero` (orthogonality to every polynomial
evaluation) through the `L²` inner product at `q = Xⁿ`. -/
theorem monomial_moment_measureT_eq_zero (g : Lp 𝕜 2 measureT)
    (hmode : ∀ n, inner 𝕜 g (normalizedChebyshevTLp 𝕜 n) = 0) (n : ℕ) :
    ∫ x, (algebraMap ℝ 𝕜 x) ^ n * g x ∂measureT = 0 := by
  -- Orthogonal to every polynomial evaluation, at the monomial `Xⁿ`.
  have hpoly : inner 𝕜 g (polynomialEvalChebyshevLp 𝕜 (X ^ n)) = 0 :=
    inner_polynomialEvalChebyshevLp_eq_zero 𝕜 g hmode (X ^ n)
  -- Flip the inner product; the monomial side is real, so its conjugate is itself.
  have hflip : inner 𝕜 (polynomialEvalChebyshevLp 𝕜 (X ^ n)) g = 0 :=
    inner_eq_zero_symm.mpr hpoly
  rw [MeasureTheory.L2.inner_def] at hflip
  rw [← hflip]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_polynomialEvalChebyshevLp 𝕜 (X ^ n)] with x hx
  rw [hx, RCLike.inner_apply, Polynomial.eval_pow, Polynomial.eval_X,
    RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal, RCLike.ofReal_pow]
  ring

/-- **Completeness of the Chebyshev family.** The orthogonal complement of the span of the
normalized modes is trivial: a vector orthogonal to all of them has vanishing monomial moments and
is therefore a.e. `0` by moment determinacy. -/
theorem orthogonal_span_normalizedChebyshevTLp_eq_bot :
    (Submodule.span 𝕜 (Set.range (normalizedChebyshevTLp 𝕜)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  have hmode : ∀ n, inner 𝕜 g (normalizedChebyshevTLp 𝕜 n) = 0 := by
    intro n
    exact inner_eq_zero_symm.mpr
      ((Submodule.mem_orthogonal _ _).mp hg _ (Submodule.subset_span ⟨n, rfl⟩))
  have hae := ae_eq_zero_of_forall_moment_eq_zero_of_exists_integrable_exp (ν := measureT)
    exp_moment_measureT (Lp.memLp g) (monomial_moment_measureT_eq_zero 𝕜 g hmode)
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr hae

/-- **Roadmap Part C: the Chebyshev `T` polynomials are a Hilbert basis of `L²(measureT)`.**
Orthonormality is `orthonormal_normalizedChebyshevTLp`; completeness is
`orthogonal_span_normalizedChebyshevTLp_eq_bot`, which is where the shipped Chebyshev groundwork had
stopped, one step short of the function-level moment-determinacy theorem. -/
noncomputable def chebyshevTHilbertBasis : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 measureT) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_normalizedChebyshevTLp
    (orthogonal_span_normalizedChebyshevTLp_eq_bot 𝕜)

/-- **The basis vectors are the normalized Chebyshev modes.** Without this the construction would
only exhibit *some* Hilbert basis of `L²(measureT)`; here each vector is pinned to `Tₙ/√‖Tₙ‖²`. -/
@[simp]
theorem coe_chebyshevTHilbertBasis :
    ⇑(chebyshevTHilbertBasis 𝕜) = normalizedChebyshevTLp 𝕜 :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

end TauCeti
