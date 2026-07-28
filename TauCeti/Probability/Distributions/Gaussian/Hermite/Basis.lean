module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness
public import TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality
public import TauCeti.Probability.Distributions.Gaussian.Hermite.MemLp

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
  exponential moment finite, the hypothesis
  `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot` needs.
* `TauCeti.gaussianHermiteHilbertBasis` — milestone A3′ itself.
* `TauCeti.coeFn_gaussianHermiteHilbertBasis` — the anti-vacuity pin: the basis vectors really are
  `Hₙ/√(n!)`, not merely *some* orthonormal basis.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Real ProbabilityTheory

/-- The standard Gaussian measure is the Lebesgue measure weighted by its own density — the shape
`TauCeti.hilbertBasisOfWeightedMeasure` produces its basis on.

Stated before the integrability and orthogonality results below because both are obtained by
transporting a `gaussianReal`-side statement along it, rather than re-proved density-side. -/
theorem gaussianReal_zero_one_eq_withDensity :
    (gaussianReal 0 1 : Measure ℝ)
      = volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  rfl

/-- **Orthogonality against the standard Gaussian density.**
`∫ Hₘ Hₙ dγ = δₘₙ · n!`. This is the density-side reading of the Gaussian-measure orthogonality
milestone `TauCeti.integral_hermite_mul_hermite_gaussianReal`: `∫ · ∂γ` unfolds to `∫ pdf • ·`, so
the two differ only by the order of the factors. -/
theorem integral_hermite_mul_hermite_mul_gaussianPDFReal (m n : ℕ) :
    (∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) * gaussianPDFReal 0 1 x)
      = if m = n then (n.factorial : ℝ) else 0 := by
  rw [← integral_hermite_mul_hermite_gaussianReal m n,
    integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  simp only [smul_eq_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-! ## The weighted-measure input data -/

/-- `Hₙ` over `ℝ`: Mathlib's `Polynomial.hermite n` lives in `ℤ[X]`, and the weighted-measure
machinery consumes a real polynomial family. -/
noncomputable def hermiteℝ (n : ℕ) : Polynomial ℝ := (hermite n).map (Int.castRingHom ℝ)

theorem eval_hermiteℝ (n : ℕ) (x : ℝ) : (hermiteℝ n).eval x = aeval x (hermite n) := by
  rw [hermiteℝ, Polynomial.eval_map, Polynomial.aeval_def]
  rfl

/-- The cast to `ℝ[X]` preserves degrees: `Hₙ` has degree exactly `n`, the exact-degree hypothesis
of `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`. -/
theorem degree_hermiteℝ (n : ℕ) : (hermiteℝ n).degree = (n : WithBot ℕ) := by
  rw [hermiteℝ, Polynomial.degree_map_eq_of_injective Int.cast_injective, Polynomial.degree_hermite]

/-- The Hermite normalization `cₙ = n!` is positive. -/
theorem hermiteGaussianNormalization_pos (n : ℕ) : (0 : ℝ) < (n.factorial : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

/-- **Finite exponential moments of the standard Gaussian.** For every rate `a`, `e^{a|x|}` is
integrable against `γ`.

Both one-sided exponentials are already integrable against a Gaussian
(`ProbabilityTheory.integrable_exp_mul_gaussianReal`, which is the mgf being everywhere finite), and
`ProbabilityTheory.integrable_exp_mul_abs` folds the rates `a` and `-a` into the two-sided
`e^{a|x|}`. Transporting along `gaussianReal_zero_one_eq_withDensity` then puts it in the
with-density form the completeness theorem takes. -/
theorem integrable_exp_mul_abs_gaussianPDFReal (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|))
      (volume.withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) := by
  rw [← gaussianReal_zero_one_eq_withDensity]
  exact integrable_exp_mul_abs (X := fun x : ℝ => x) (t := a)
    (integrable_exp_mul_gaussianReal a) (integrable_exp_mul_gaussianReal (-a))

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
    (orthogonal_span_range_bareNormalizedLp_eq_bot (𝕜 := 𝕜) hermiteℝ
      (fun x => gaussianPDFReal 0 1 x)
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
determinacy (`TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`), applied to the exact-degree
family `Hₙ`.
Where `TauCeti.hermiteHilbertBasis` carries the Gaussian in the function, this carries it in the
measure — the form multivariate `L²(γ^ι)` and chaos expansions consume. -/
noncomputable def gaussianHermiteHilbertBasis :
    HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (gaussianReal 0 1)) :=
  cast (by rw [gaussianReal_zero_one_eq_withDensity]) (gaussianHermiteHilbertBasisAux 𝕜)

/-- **The basis vectors are the normalized Hermite polynomials.** Without this the construction
would only exhibit *some* Hilbert basis of `L²(γ)`; here each vector is pinned to `Hₙ/√(n!)`, which
is what downstream chaos-coordinate computations need. -/
theorem coeFn_gaussianHermiteHilbertBasis (n : ℕ) :
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
