/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import TauCeti.MeasureTheory.Function.PolynomialMemLp

/-!
# Polynomial moments for the Chebyshev `T` measure

This file records bare-polynomial moment, `L¹`, and `L²` consequences of compact support for
Mathlib's Chebyshev orthogonality measure `Polynomial.Chebyshev.measureT`.

The normalized Chebyshev modes and their orthonormality live in
`TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure`.  The lemmas here are the
un-normalized consumer forms needed on the way to the roadmap's Chebyshev Hilbert-basis target:
every real polynomial moment is finite, every real polynomial evaluation is integrable and square
integrable, and these statements are available after casting real-valued functions to any
`[RCLike 𝕜]` scalar field.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

/-- Every real monomial has finite `L¹` moment with respect to the Chebyshev `T` measure. -/
lemma integrable_pow_measureT (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) Polynomial.Chebyshev.measureT :=
  integrable_measureT (by fun_prop)

/-- A real polynomial evaluation is integrable with respect to the Chebyshev `T` measure. -/
lemma integrable_eval_measureT (q : Polynomial ℝ) :
    Integrable (fun x : ℝ => q.eval x) Polynomial.Chebyshev.measureT :=
  integrable_eval_of_forall_integrable_pow integrable_pow_measureT q

/-- A real polynomial evaluation, cast to any `RCLike` scalar field, is integrable with respect
to the Chebyshev `T` measure. -/
lemma integrable_algebraMap_eval_measureT {𝕜 : Type*} [RCLike 𝕜] (q : Polynomial ℝ) :
    Integrable (fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x))
      Polynomial.Chebyshev.measureT := by
  simpa only [RCLike.algebraMap_eq_ofReal] using
    (integrable_eval_measureT q).ofReal (𝕜 := 𝕜)

/-- A real polynomial evaluation lies in `L²` with respect to the Chebyshev `T` measure. -/
lemma memLp_two_eval_measureT (q : Polynomial ℝ) :
    MemLp (fun x : ℝ => q.eval x) 2 Polynomial.Chebyshev.measureT :=
  memLp_two_eval_of_forall_integrable_pow integrable_pow_measureT q

/-- A real polynomial evaluation, cast to any `RCLike` scalar field, lies in `L²` with respect
to the Chebyshev `T` measure. -/
lemma memLp_two_algebraMap_eval_measureT {𝕜 : Type*} [RCLike 𝕜] (q : Polynomial ℝ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x)) 2
      Polynomial.Chebyshev.measureT := by
  simpa only [RCLike.algebraMap_eq_ofReal] using
    (memLp_two_eval_measureT q).ofReal (K := 𝕜)

/-- Evaluate a real polynomial and, casting into any `[RCLike 𝕜]` scalar field, regard the result
as an element of `L²(Polynomial.Chebyshev.measureT)`.

The map is well-defined because every polynomial has finite second moment for the Chebyshev
measure. -/
noncomputable def polynomialEvalChebyshevLp (𝕜 : Type*) [RCLike 𝕜] :
    Polynomial ℝ →ₗ[ℝ] Lp 𝕜 2 Polynomial.Chebyshev.measureT :=
  polynomialEvalLp 𝕜 integrable_pow_measureT

/-- The `L²` representative of a polynomial evaluation is the expected scalar-cast pointwise
evaluation. -/
lemma coeFn_polynomialEvalChebyshevLp (𝕜 : Type*) [RCLike 𝕜] (q : Polynomial ℝ) :
    ⇑(polynomialEvalChebyshevLp 𝕜 q) =ᵐ[Polynomial.Chebyshev.measureT]
      fun x => (algebraMap ℝ 𝕜) (q.eval x) :=
  coeFn_polynomialEvalLp 𝕜 integrable_pow_measureT q

end TauCeti
