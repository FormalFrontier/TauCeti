/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Orthonormal

/-!
# The Hermite functions as a Hilbert basis of `L²(ℝ)`

This file instantiates the weighted-measure machinery at the Gaussian weight `w(x) = e^{-x²}` and
the dilated Hermite polynomials `Hₙ(x√2)`, whose `√w`-envelope is exactly the Hermite function
`ψₙ` of `TauCeti.hermiteFunction`.

## Main statements

* `TauCeti.integrable_exp_mul_abs_gaussianWeight` — the Gaussian weight has every exponential
  moment finite, the hypothesis the completeness theorem
  `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot` needs.
* `TauCeti.degree_hermiteDilated` — `Hₙ(x√2)` has degree exactly `n`.
* `TauCeti.integral_hermiteDilated_mul_hermiteDilated_mul_gaussianWeight` — the orthogonality
  relation with normalization `cₙ = n!√π`, obtained from the Hermite function orthonormality
  (milestone A2).
* `TauCeti.hermiteHilbertBasis` — **milestone A3**: the Hermite functions as a `HilbertBasis` of
  `L²(ℝ)`, the principal result of this file.
* `TauCeti.coe_hermiteHilbertBasis` — its normal form: the `n`-th basis vector really is `ψₙ`.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Real

/-- The dilation preserves degrees: `Hₙ(√2 · X)` has degree exactly `n`.

`TauCeti.hermiteDilated` itself lives in the `MemLp` layer, where the membership results are
already stated about it; only this degree fact is new here, and only the basis construction
needs it. -/
theorem degree_hermiteDilated (n : ℕ) : (hermiteDilated n).degree = (n : WithBot ℕ) := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hq : (Polynomial.C (Real.sqrt 2) * Polynomial.X).degree = 1 :=
    Polynomial.degree_C_mul_X h2
  rw [hermiteDilated_def, Polynomial.degree_comp (by rw [hq]; norm_num), hq, degree_hermiteℝ,
    mul_one]

/-- **Finite exponential moments of a Gaussian weight.** For every rate `a` and every width
`b > 0`, the function `e^{a|x|}` is integrable against `e^{-bx²}·dx`, because
`a|x| ≤ a²/(2b) + bx²/2` gives the domination `e^{a|x|}e^{-bx²} ≤ e^{a²/(2b)}·e^{-bx²/2}`.

The width is left general because the Hermite family appears against two different Gaussian
weights: `e^{-x²}` for the basis of `L²(ℝ)` in the angular-frequency normalization, and
`e^{-2πx²}` for the Fourier-adapted rescaling. -/
theorem integrable_exp_mul_abs_gaussianWeight {b : ℝ} (hb : 0 < b) (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|))
      (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-(b * x ^ 2)))) := by
  have hgauss :
      Integrable (fun x : ℝ => Real.exp (a ^ 2 / (2 * b)) * Real.exp (-(b / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : (0:ℝ) < b / 2)).const_mul _
  have hcore : Integrable (fun x : ℝ => Real.exp (a * |x|) * Real.exp (-(b * x ^ 2))) := by
    refine hgauss.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [← Real.exp_add, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    -- Cleared of the denominator `2b`, the bound is exactly `0 ≤ (a - b|x|)²`.
    have hsq : 0 ≤ a ^ 2 - 2 * (a * b) * |x| + b ^ 2 * x ^ 2 := by
      have h : (a - b * |x|) ^ 2 = a ^ 2 - 2 * (a * b) * |x| + b ^ 2 * x ^ 2 := by
        rw [← sq_abs x]; ring
      exact h ▸ sq_nonneg _
    have hkey : a * |x| - b / 2 * x ^ 2 ≤ a ^ 2 / (2 * b) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)]
      nlinarith [hsq]
    linarith
  rw [integrable_withDensity_iff_integrable_smul₀' (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hfun :
      (fun x : ℝ => (ENNReal.ofReal (Real.exp (-(b * x ^ 2)))).toReal • Real.exp (a * |x|))
        = fun x : ℝ => Real.exp (a * |x|) * Real.exp (-(b * x ^ 2)) := by
    funext x
    rw [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_comm]
  rw [hfun]
  exact hcore

/-- The exponential-moment hypothesis of the completeness theorem, at the width-`1` Gaussian
weight `e^{-x²}` this file works with. -/
private theorem exp_moment_gaussianWeight :
    ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|))
      (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-x ^ 2))) :=
  ⟨1, one_pos, by simpa using integrable_exp_mul_abs_gaussianWeight one_pos 1⟩

/-- The Hermite normalization `cₙ = n!·√π` is positive. -/
theorem hermiteNormalization_pos (n : ℕ) : (0 : ℝ) < (n.factorial : ℝ) * Real.sqrt Real.pi := by
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- **Orthogonality against the Gaussian weight.** `∫ Hₘ(x√2)Hₙ(x√2)e^{-x²} = δₘₙ·n!√π`. This is
the Hermite function orthonormality (milestone A2) with the normalizations put back. -/
theorem integral_hermiteDilated_mul_hermiteDilated_mul_gaussianWeight (m n : ℕ) :
    (∫ x : ℝ, (hermiteDilated m).eval x * (hermiteDilated n).eval x * Real.exp (-x ^ 2))
      = if m = n then (n.factorial : ℝ) * Real.sqrt Real.pi else 0 := by
  have hpt : ∀ x : ℝ, (hermiteDilated m).eval x * (hermiteDilated n).eval x * Real.exp (-x ^ 2)
      = (Real.sqrt ((m.factorial : ℝ) * Real.sqrt Real.pi)
          * Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))
        * (hermiteFunction m x * hermiteFunction n x) := by
    intro x
    have he : Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2)) = Real.exp (-x ^ 2) := by
      rw [← Real.exp_add]
      ring_nf
    have hm : Real.sqrt ((m.factorial : ℝ) * Real.sqrt Real.pi) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hermiteNormalization_pos m))
    have hn : Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (hermiteNormalization_pos n))
    rw [eval_hermiteDilated, eval_hermiteDilated, hermiteFunction_def, hermiteFunction_def, ← he]
    field_simp
  simp_rw [hpt]
  rw [integral_const_mul, integral_hermiteFunction_mul_hermiteFunction]
  by_cases hmn : m = n
  · subst hmn
    rw [if_pos rfl, if_pos rfl, mul_one,
      Real.mul_self_sqrt (hermiteNormalization_pos m).le]
  · rw [if_neg hmn, if_neg hmn, mul_zero]

section Basis

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The `MemLp` obligation for the dilated Hermite family against the Gaussian weight. This is the
generic `TauCeti.memLp_two_bareNormalized` at `p = hermiteDilated`, `c n = n!√π`; the only content
specific to this family is the exponential moment of `e^{-x²}`. -/
private theorem memLp_hermiteDilated_normalized (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜)
        ((hermiteDilated n).eval x / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))) 2
      (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-x ^ 2))) :=
  memLp_two_bareNormalized (𝕜 := 𝕜) exp_moment_gaussianWeight
    hermiteDilated (fun n => (n.factorial : ℝ) * Real.sqrt Real.pi) n

/-- **Roadmap A3: the Hermite functions are a Hilbert basis of `L²(ℝ)`.** Orthonormality comes from
the weighted-measure machinery and completeness from moment determinacy
(`TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`), applied to the exact-degree family
`Hₙ(x√2)` against the Gaussian weight `e^{-x²}`. -/
noncomputable def hermiteHilbertBasis : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (volume : Measure ℝ)) :=
  hilbertBasisOfOrthogonalSystem (𝕜 := 𝕜) (fun n x => (hermiteDilated n).eval x)
    (fun x => Real.exp (-x ^ 2)) (fun n => (n.factorial : ℝ) * Real.sqrt Real.pi)
    (Filter.Eventually.of_forall fun x => Real.exp_pos _) (by fun_prop)
    hermiteNormalization_pos
    (fun m n => by
      simpa using integral_hermiteDilated_mul_hermiteDilated_mul_gaussianWeight m n)
    (memLp_hermiteDilated_normalized 𝕜)
    (orthogonal_span_range_bareNormalizedLp_eq_bot (𝕜 := 𝕜) hermiteDilated
      (fun x => Real.exp (-x ^ 2))
      (fun n => (n.factorial : ℝ) * Real.sqrt Real.pi) degree_hermiteDilated
      hermiteNormalization_pos exp_moment_gaussianWeight
      (memLp_hermiteDilated_normalized 𝕜))

/-- **The basis vectors are the Hermite functions.** Without this the construction would only
exhibit *some* Hilbert basis; here the `√w`-envelope of `Hₙ(x√2)/√cₙ` is identified with `ψₙ`. -/
@[simp]
theorem coe_hermiteHilbertBasis : ⇑(hermiteHilbertBasis 𝕜) = hermiteFunctionLp 𝕜 := by
  funext n
  rw [hermiteHilbertBasis]
  -- The bridge already presents the `n`-th vector as `Hₙ(x√2)·√w/√cₙ`, so nothing about the
  -- weighted measure is left to do here.
  refine Lp.ext ((coeFn_hilbertBasisOfOrthogonalSystem _ _ _ _ _ _ _ _ _ n).trans ?_)
  filter_upwards [coeFn_hermiteFunctionLp (𝕜 := 𝕜) n] with x hx
  -- `√w` is the Hermite envelope: `√(e^{-x²}) = e^{-x²/2}`. `Real.sqrt_mul_self` wants the
  -- radicand presented as a literal product, so the exponent is split first and `Real.exp_add`
  -- turns the sum into that product; the split is stated as its own equality rather than being
  -- reshaped inline.
  have hsplit : (-x ^ 2 : ℝ) = -(x ^ 2 / 2) + -(x ^ 2 / 2) := by ring
  have hs : Real.sqrt (Real.exp (-x ^ 2)) = Real.exp (-(x ^ 2 / 2)) := by
    rw [hsplit, Real.exp_add]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  rw [hx, hermiteFunction_def, eval_hermiteDilated, hs]

end Basis

end TauCeti
