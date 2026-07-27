module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness
public import TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality
public import TauCeti.Probability.Distributions.Gaussian.HermiteMemLp

/-!
# The Hermite polynomials as a Hilbert basis of `L²(γ)`

Roadmap milestone **A3′**: the measure-side one-dimensional Gaussian Hermite basis. Where
`TauCeti.hermiteHilbertBasis` puts the Gaussian envelope inside the *function* (`ψₙ` in `L²(ℝ)`),
this puts it in the *measure*: `Hₙ/√(n!)` is an orthonormal basis of `L²(γ)` for the standard
Gaussian `γ = gaussianReal 0 1`.

That is the form multivariate Gaussian `L²` and chaos expansions consume, and it is the input
`piHilbertBasis` needs for the multidimensional basis of Part D.

## Main statements

* `TauCeti.integral_hermite_mul_hermite_mul_gaussianPDFReal` — the orthogonality relation against
  the standard Gaussian density, with normalization `cₙ = n!`.
* `TauCeti.integrable_exp_mul_abs_gaussianPDFReal` — the standard Gaussian density has every
  exponential moment finite, the hypothesis `TauCeti.bareNormalizedLp_ortho_eq_bot` needs.
* `TauCeti.gaussianHermiteHilbertBasis` — milestone A3′ itself.
* `TauCeti.coe_gaussianHermiteHilbertBasis` — the anti-vacuity pin: the basis vectors really are
  `Hₙ/√(n!)`, not merely *some* orthonormal basis.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Real ProbabilityTheory

/-- The standard Gaussian density is `(√(2π))⁻¹·e^{-x²/2}`. -/
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  rw [gaussianPDFReal_def]
  norm_num
  exact Or.inl (by ring)

/-- **Orthogonality against the standard Gaussian density.**
`∫ Hₘ Hₙ dγ = δₘₙ · n!`. This is the Hermite orthogonality relation (milestone A1) divided by the
Gaussian normalizing constant `√(2π)`, which is exactly what turns the `n!√(2π)` there into the
`cₙ = n!` the measure-side basis uses. -/
theorem integral_hermite_mul_hermite_mul_gaussianPDFReal (m n : ℕ) :
    (∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) * gaussianPDFReal 0 1 x)
      = if m = n then (n.factorial : ℝ) else 0 := by
  have h2pi : Real.sqrt (2 * π) ≠ 0 := by
    have : (0 : ℝ) < 2 * π := by positivity
    exact ne_of_gt (Real.sqrt_pos.mpr this)
  have hpt : ∀ x : ℝ, aeval x (hermite m) * aeval x (hermite n) * gaussianPDFReal 0 1 x
      = (Real.sqrt (2 * π))⁻¹
        * (aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))) := by
    intro x
    rw [gaussianPDFReal_zero_one]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_hermite_mul_hermite_mul_gaussian]
  by_cases hmn : m = n
  · rw [if_pos hmn, if_pos hmn]
    field_simp
  · rw [if_neg hmn, if_neg hmn, mul_zero]

/-! ## The weighted-measure input data -/

/-- `Hₙ` over `ℝ`: Mathlib's `Polynomial.hermite n` lives in `ℤ[X]`, and the weighted-measure
machinery consumes a real polynomial family. -/
noncomputable def hermiteℝ (n : ℕ) : Polynomial ℝ := (hermite n).map (Int.castRingHom ℝ)

theorem eval_hermiteℝ (n : ℕ) (x : ℝ) : (hermiteℝ n).eval x = aeval x (hermite n) := by
  rw [hermiteℝ, Polynomial.eval_map, Polynomial.aeval_def]
  rfl

/-- The cast to `ℝ[X]` preserves degrees: `Hₙ` has degree exactly `n`, the exact-degree hypothesis
of `TauCeti.bareNormalizedLp_ortho_eq_bot`. -/
theorem degree_hermiteℝ (n : ℕ) : (hermiteℝ n).degree = (n : WithBot ℕ) := by
  rw [hermiteℝ, Polynomial.degree_map_eq_of_injective Int.cast_injective, Polynomial.degree_hermite]

/-- The Hermite normalization `cₙ = n!` is positive. -/
theorem hermiteGaussianNormalization_pos (n : ℕ) : (0 : ℝ) < (n.factorial : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

/-- The standard Gaussian measure is the Lebesgue measure weighted by its own density — the shape
`TauCeti.hilbertBasisOfWeightedMeasure` produces its basis on. -/
theorem gaussianReal_zero_one_eq_withDensity :
    (gaussianReal 0 1 : Measure ℝ)
      = volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  rfl

/-- **Finite exponential moments of the standard Gaussian.** For every rate `a`, `e^{a|x|}` is
integrable against `γ`, because `a|x| ≤ a² + x²/4` gives the domination
`e^{a|x|}e^{-x²/2} ≤ e^{a²}·e^{-x²/4}`. Note the spare Gaussian is `e^{-x²/4}`, not the `e^{-x²/2}`
of the function-side weight: here the density itself is only `e^{-x²/2}`. -/
theorem integrable_exp_mul_abs_gaussianPDFReal (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|))
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) := by
  have h2pi : (0 : ℝ) < (Real.sqrt (2 * π))⁻¹ := by
    have h : (0 : ℝ) < 2 * π := by positivity
    have := Real.sqrt_pos.mpr h
    positivity
  have hgauss : Integrable (fun x : ℝ =>
      (Real.sqrt (2 * π))⁻¹ * Real.exp (a ^ 2) * Real.exp (-(1 / 4) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 4)).const_mul _
  have hcore : Integrable (fun x : ℝ => Real.exp (a * |x|) * gaussianPDFReal 0 1 x) := by
    refine hgauss.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    have hnn : (0 : ℝ) ≤ Real.exp (a * |x|) * gaussianPDFReal 0 1 x := by
      have := gaussianPDFReal_nonneg 0 1 x
      positivity
    have hkey : Real.exp (a * |x|) * Real.exp (-(x ^ 2 / 2))
        ≤ Real.exp (a ^ 2) * Real.exp (-(1 / 4) * x ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [sq_nonneg (|x| - 2 * a), sq_abs x, abs_nonneg x]
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, gaussianPDFReal_zero_one]
    calc Real.exp (a * |x|) * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)))
        = (Real.sqrt (2 * π))⁻¹ * (Real.exp (a * |x|) * Real.exp (-(x ^ 2 / 2))) := by ring
      _ ≤ (Real.sqrt (2 * π))⁻¹ * (Real.exp (a ^ 2) * Real.exp (-(1 / 4) * x ^ 2)) :=
          mul_le_mul_of_nonneg_left hkey h2pi.le
      _ = (Real.sqrt (2 * π))⁻¹ * Real.exp (a ^ 2) * Real.exp (-(1 / 4) * x ^ 2) := by ring
  rw [integrable_withDensity_iff_integrable_smul₀' (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hfun : (fun x : ℝ =>
        (ENNReal.ofReal (gaussianPDFReal 0 1 x)).toReal • Real.exp (a * |x|))
      = fun x : ℝ => Real.exp (a * |x|) * gaussianPDFReal 0 1 x := by
    funext x
    rw [smul_eq_mul, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x), mul_comm]
  rw [hfun]
  exact hcore

/-- The exponential-moment hypothesis in the existential form the completeness theorem takes. -/
theorem exp_moment_gaussianPDFReal :
    ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|))
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) :=
  ⟨1, one_pos, integrable_exp_mul_abs_gaussianPDFReal 1⟩

section Basis

variable (𝕜 : Type*) [RCLike 𝕜]

private theorem memLp_hermiteℝ_normalized (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜)
        ((hermiteℝ n).eval x / Real.sqrt ((n.factorial : ℝ)))) 2
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) := by
  rw [← gaussianReal_zero_one_eq_withDensity]
  simpa only [eval_hermiteℝ] using memLp_hermite_gaussianReal (𝕜 := 𝕜) n 1

/-- The basis in the weighted-measure form the machinery produces; `gaussianHermiteHilbertBasis`
is this transported along `gaussianReal_zero_one_eq_withDensity`. -/
private noncomputable def gaussianHermiteHilbertBasisAux :
    HilbertBasis ℕ 𝕜
      (Lp 𝕜 2 (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))) :=
  hilbertBasisOfWeightedMeasure (𝕜 := 𝕜) (fun n x => (hermiteℝ n).eval x)
    (fun x => gaussianPDFReal 0 1 x) (fun n => (n.factorial : ℝ))
    (Filter.Eventually.of_forall fun x => gaussianPDFReal_nonneg 0 1 x) (by fun_prop)
    hermiteGaussianNormalization_pos
    (fun m n => by
      simpa only [eval_hermiteℝ] using integral_hermite_mul_hermite_mul_gaussianPDFReal m n)
    (memLp_hermiteℝ_normalized 𝕜)
    (bareNormalizedLp_ortho_eq_bot (𝕜 := 𝕜) hermiteℝ (fun x => gaussianPDFReal 0 1 x)
      (fun n => (n.factorial : ℝ)) degree_hermiteℝ hermiteGaussianNormalization_pos
      exp_moment_gaussianPDFReal (memLp_hermiteℝ_normalized 𝕜))

/-- Transporting a basis along an equality of measures does not change its vectors: the `cast` is
along `Lp 𝕜 2 μ = Lp 𝕜 2 ν`, so it acts as the identity on representatives. -/
private theorem coe_cast_hilbertBasis {μ ν : Measure ℝ} (h : μ = ν)
    (hty : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 μ) = HilbertBasis ℕ 𝕜 (Lp 𝕜 2 ν))
    (b : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 μ)) (n : ℕ) {g : ℝ → 𝕜} (hb : ⇑(b n) =ᵐ[μ] g) :
    ⇑((cast hty b) n) =ᵐ[ν] g := by
  subst h
  rw [cast_eq]
  exact hb

/-- **Roadmap A3′: the Hermite polynomials are a Hilbert basis of `L²(γ)`.** Orthonormality comes
from the orthogonality relation against the Gaussian density and completeness from moment
determinacy (`TauCeti.bareNormalizedLp_ortho_eq_bot`), applied to the exact-degree family `Hₙ`.
Where `TauCeti.hermiteHilbertBasis` carries the Gaussian in the function, this carries it in the
measure — the form multivariate `L²(γ^ι)` and chaos expansions consume. -/
noncomputable def gaussianHermiteHilbertBasis :
    HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (gaussianReal 0 1)) :=
  cast (by rw [gaussianReal_zero_one_eq_withDensity]) (gaussianHermiteHilbertBasisAux 𝕜)

/-- **The basis vectors are the normalized Hermite polynomials.** Without this the construction
would only exhibit *some* Hilbert basis of `L²(γ)`; here each vector is pinned to `Hₙ/√(n!)`, which
is what downstream chaos-coordinate computations need. -/
theorem coe_gaussianHermiteHilbertBasis (n : ℕ) :
    ⇑(gaussianHermiteHilbertBasis 𝕜 n) =ᵐ[gaussianReal 0 1]
      fun x => (algebraMap ℝ 𝕜) (aeval x (hermite n) / Real.sqrt ((n.factorial : ℝ))) := by
  have hcoe : ⇑(gaussianHermiteHilbertBasisAux 𝕜)
      = bareNormalizedLp (𝕜 := 𝕜) (fun n x => (hermiteℝ n).eval x)
        (fun x => gaussianPDFReal 0 1 x) (fun n => (n.factorial : ℝ))
        (memLp_hermiteℝ_normalized 𝕜) :=
    coe_hilbertBasisOfWeightedMeasure _ _ _ _ _ _ _ _ _
  have haux : ⇑(gaussianHermiteHilbertBasisAux 𝕜 n)
      =ᵐ[volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)]
        fun x => (algebraMap ℝ 𝕜) (aeval x (hermite n) / Real.sqrt ((n.factorial : ℝ))) := by
    rw [hcoe]
    filter_upwards [coeFn_bareNormalizedLp (𝕜 := 𝕜) (fun n x => (hermiteℝ n).eval x)
      (fun x => gaussianPDFReal 0 1 x) (fun n => (n.factorial : ℝ))
      (memLp_hermiteℝ_normalized 𝕜) n] with x hx
    rw [hx, eval_hermiteℝ]
  rw [gaussianHermiteHilbertBasis]
  exact coe_cast_hilbertBasis 𝕜 gaussianReal_zero_one_eq_withDensity.symm _ _ n haux

end Basis

end TauCeti
