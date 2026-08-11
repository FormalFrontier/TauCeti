/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Moments
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure
import TauCeti.RingTheory.Polynomial.Chebyshev.Basis

/-!
# Polynomial span of the Chebyshev modes

This file connects the algebraic Chebyshev basis of `ℝ[X]` with the normalized Chebyshev
functions in `L²(Polynomial.Chebyshev.measureT)`.  Evaluation followed by the canonical map into
`L²` is bundled as a linear map.  Since every Chebyshev polynomial is a nonzero scalar multiple
of its normalized mode, every polynomial evaluation belongs to the linear span of those modes.

This is the algebra-to-analysis handoff in Part C of the `OrthogonalL2Bases` roadmap.  In the
completeness argument, it upgrades orthogonality against every Chebyshev mode to orthogonality
against every polynomial.

## Main declarations

* `TauCeti.polynomialEvalChebyshevLp`: polynomial evaluation, cast into any `[RCLike 𝕜]` scalar
  field, as a linear map into `L²(Polynomial.Chebyshev.measureT)`.
* `TauCeti.polynomialEvalChebyshevLp_mem_span`: every polynomial evaluation lies in the span of
  the normalized Chebyshev modes.
* `TauCeti.inner_polynomialEvalChebyshevLp_eq_zero`: orthogonality to all normalized modes implies
  orthogonality to every polynomial evaluation.
* `TauCeti.inner_polynomialEvalChebyshevLp`: the inner product against a polynomial evaluation is
  the corresponding polynomial moment `∫ x, g x * q.eval x ∂measureT`.
* `TauCeti.integral_polynomialEval_measureT_eq_zero`: orthogonality to all normalized modes makes
  every polynomial moment vanish.

The measure- and scalar-generic bundling of polynomial evaluation lives in
`TauCeti.MeasureTheory.Function.PolynomialMemLp` as `polynomialEvalLp`; `polynomialEvalChebyshevLp`
is its Chebyshev specialization.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

/-- Under the polynomial-evaluation map, the `n`th Chebyshev polynomial is the square root of its
squared norm times the normalized `n`th Chebyshev mode. -/
lemma polynomialEvalChebyshevLp_T (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    polynomialEvalChebyshevLp 𝕜 (T ℝ n) =
      Real.sqrt (chebyshevTNormSq n) • normalizedChebyshevTLp 𝕜 n := by
  apply Lp.ext
  filter_upwards [coeFn_polynomialEvalChebyshevLp 𝕜 (T ℝ n),
    coeFn_normalizedChebyshevTLp (𝕜 := 𝕜) n,
    Lp.coeFn_smul (Real.sqrt (chebyshevTNormSq n)) (normalizedChebyshevTLp 𝕜 n)] with
      x hT hnorm hsmul
  rw [hT, hsmul]
  simp only [Pi.smul_apply]
  rw [hnorm, normalizedChebyshevT_def, Algebra.smul_def, ← map_mul]
  congr 1
  field_simp [Real.sqrt_ne_zero'.mpr (chebyshevTNormSq_pos n)]

/-- Every real polynomial evaluation in `L²(measureT)` belongs to the linear span of the
normalized Chebyshev modes. -/
theorem polynomialEvalChebyshevLp_mem_span (𝕜 : Type*) [RCLike 𝕜] (q : Polynomial ℝ) :
    polynomialEvalChebyshevLp 𝕜 q ∈
      Submodule.span 𝕜 (Set.range (normalizedChebyshevTLp 𝕜)) := by
  let S := Submodule.span 𝕜 (Set.range (normalizedChebyshevTLp 𝕜))
  have hq : q ∈ Submodule.span ℝ (Set.range (chebyshevTBasis (R := ℝ))) := by
    rw [Module.Basis.span_eq]
    exact Submodule.mem_top
  refine Submodule.span_induction ?_
    ((polynomialEvalChebyshevLp 𝕜).map_zero ▸ S.zero_mem)
    (fun _ _ _ _ hx hy => by simpa using S.add_mem hx hy)
    (fun a _ _ hx => by
      rw [map_smul, algebra_compatible_smul 𝕜 a]
      exact S.smul_mem _ hx) hq
  rintro p ⟨n, rfl⟩
  rw [chebyshevTBasis_apply, polynomialEvalChebyshevLp_T, algebra_compatible_smul 𝕜]
  exact S.smul_mem _ (Submodule.subset_span (Set.mem_range_self n))

/-- A vector orthogonal to every normalized Chebyshev mode is orthogonal to the `L²` evaluation
of every real polynomial.

This is the abstract form used in the Chebyshev completeness argument: the algebraic Chebyshev
basis converts the mode hypotheses into orthogonality against every polynomial evaluation. -/
theorem inner_polynomialEvalChebyshevLp_eq_zero (𝕜 : Type*) [RCLike 𝕜]
    (g : Lp 𝕜 2 Polynomial.Chebyshev.measureT)
    (hmode : ∀ n, inner 𝕜 g (normalizedChebyshevTLp 𝕜 n) = 0) (q : Polynomial ℝ) :
    inner 𝕜 g (polynomialEvalChebyshevLp 𝕜 q) = 0 := by
  have hmem := polynomialEvalChebyshevLp_mem_span 𝕜 q
  refine Submodule.span_induction ?_ (by simp)
    (fun _ _ _ _ hx hy => by simp [inner_add_right, hx, hy])
    (fun _ _ _ hx => by simp [inner_smul_right, hx]) hmem
  rintro v ⟨n, rfl⟩
  exact hmode n

/-- The inner product of a vector with a polynomial evaluation is the corresponding polynomial
moment against the Chebyshev measure. -/
lemma inner_polynomialEvalChebyshevLp (g : Lp ℝ 2 Polynomial.Chebyshev.measureT)
    (q : Polynomial ℝ) :
    inner ℝ g (polynomialEvalChebyshevLp ℝ q) =
      ∫ x, g x * q.eval x ∂Polynomial.Chebyshev.measureT := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_polynomialEvalChebyshevLp ℝ q] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-- A vector orthogonal to every normalized Chebyshev mode has vanishing polynomial moments: this
is the concrete integral form of `inner_polynomialEvalChebyshevLp_eq_zero`. -/
theorem integral_polynomialEval_measureT_eq_zero (g : Lp ℝ 2 Polynomial.Chebyshev.measureT)
    (hmode : ∀ n, inner ℝ g (normalizedChebyshevTLp ℝ n) = 0) (q : Polynomial ℝ) :
    ∫ x, g x * q.eval x ∂Polynomial.Chebyshev.measureT = 0 := by
  rw [← inner_polynomialEvalChebyshevLp g q]
  exact inner_polynomialEvalChebyshevLp_eq_zero ℝ g hmode q

end TauCeti
