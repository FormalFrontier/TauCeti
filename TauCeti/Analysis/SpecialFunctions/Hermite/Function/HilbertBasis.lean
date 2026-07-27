module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Orthonormal

/-!
# The Hermite functions as a Hilbert basis of `L²(ℝ)`

This file instantiates the weighted-measure machinery at the Gaussian weight `w(x) = e^{-x²}` and
the dilated Hermite polynomials `Hₙ(x√2)`, whose `√w`-envelope is exactly the Hermite function
`ψₙ` of `TauCeti.hermiteFunction`.

## Main statements

* `TauCeti.integrable_exp_mul_abs_gaussianWeight` — the Gaussian weight has every exponential
  moment finite, the hypothesis `TauCeti.bareNormalizedLp_ortho_eq_bot` needs.
* `TauCeti.degree_hermiteDilated` — `Hₙ(x√2)` has degree exactly `n`.
* `TauCeti.integral_hermiteDilated_mul_gaussianWeight` — the orthogonality relation with
  normalization `cₙ = n!√π`, obtained from the Hermite function orthonormality (milestone A2).
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Real

/-- The dilated Hermite polynomial `Hₙ(√2 · X)`, the polynomial whose Gaussian envelope is the
Hermite function `ψₙ`. -/
noncomputable def hermiteDilated (n : ℕ) : Polynomial ℝ :=
  ((hermite n).map (Int.castRingHom ℝ)).comp (Polynomial.C (Real.sqrt 2) * Polynomial.X)

theorem eval_hermiteDilated (n : ℕ) (x : ℝ) :
    (hermiteDilated n).eval x = aeval (x * Real.sqrt 2) (hermite n) := by
  rw [hermiteDilated, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_map, Polynomial.aeval_def, mul_comm]
  rfl

/-- The dilation preserves degrees: `Hₙ(√2 · X)` has degree exactly `n`. -/
theorem degree_hermiteDilated (n : ℕ) : (hermiteDilated n).degree = (n : WithBot ℕ) := by
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hq : (Polynomial.C (Real.sqrt 2) * Polynomial.X).degree = 1 :=
    Polynomial.degree_C_mul_X h2
  have hmap : ((hermite n).map (Int.castRingHom ℝ)).degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_map_eq_of_injective Int.cast_injective, Polynomial.degree_hermite]
  rw [hermiteDilated, Polynomial.degree_comp (by rw [hq]; norm_num), hq, hmap, mul_one]

/-- **Finite exponential moments of the Gaussian weight.** For every rate `a`, `e^{a|x|}` is
integrable against `e^{-x²}·dx`, because `a|x| ≤ (a² + x²)/2` gives the domination
`e^{a|x|}e^{-x²} ≤ e^{a²/2}·e^{-x²/2}`. -/
theorem integrable_exp_mul_abs_gaussianWeight (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|))
      (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-x ^ 2))) := by
  have hgauss : Integrable (fun x : ℝ => Real.exp (a ^ 2 / 2) * Real.exp (-(1 / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul _
  have hcore : Integrable (fun x : ℝ => Real.exp (a * |x|) * Real.exp (-x ^ 2)) := by
    refine hgauss.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [← Real.exp_add, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [sq_nonneg (|x| - a), sq_abs x, abs_nonneg x]
  rw [integrable_withDensity_iff_integrable_smul₀' (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hfun : (fun x : ℝ => (ENNReal.ofReal (Real.exp (-x ^ 2))).toReal • Real.exp (a * |x|))
      = fun x : ℝ => Real.exp (a * |x|) * Real.exp (-x ^ 2) := by
    funext x
    rw [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_comm]
  rw [hfun]
  exact hcore

/-- The Hermite normalization `cₙ = n!·√π` is positive. -/
theorem hermiteNormalization_pos (n : ℕ) : (0 : ℝ) < (n.factorial : ℝ) * Real.sqrt Real.pi := by
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- **Orthogonality against the Gaussian weight.** `∫ Hₘ(x√2)Hₙ(x√2)e^{-x²} = δₘₙ·n!√π`. This is
the Hermite function orthonormality (milestone A2) with the normalizations put back. -/
theorem integral_hermiteDilated_mul_gaussianWeight (m n : ℕ) :
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

private theorem memLp_hermiteDilated_normalized (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜)
        ((hermiteDilated n).eval x / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))) 2
      (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-x ^ 2))) := by
  have hfun : (fun x : ℝ => (algebraMap ℝ 𝕜)
        ((hermiteDilated n).eval x / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)))
      = fun x : ℝ => (algebraMap ℝ 𝕜)
          (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))⁻¹
        * (algebraMap ℝ 𝕜) ((hermiteDilated n).eval x) := by
    funext x
    rw [← map_mul]
    congr 1
    ring
  rw [hfun]
  exact (memLp_two_algebraMap_eval (𝕜 := 𝕜)
    ⟨1, one_pos, integrable_exp_mul_abs_gaussianWeight 1⟩ (hermiteDilated n)).const_mul _

/-- **Roadmap A3: the Hermite functions are a Hilbert basis of `L²(ℝ)`.** Orthonormality comes from
the weighted-measure machinery and completeness from moment determinacy
(`TauCeti.bareNormalizedLp_ortho_eq_bot`), applied to the exact-degree family `Hₙ(x√2)` against the
Gaussian weight `e^{-x²}`. -/
noncomputable def hermiteHilbertBasis : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (volume : Measure ℝ)) :=
  hilbertBasisOfOrthogonalSystem (𝕜 := 𝕜) (fun n x => (hermiteDilated n).eval x)
    (fun x => Real.exp (-x ^ 2)) (fun n => (n.factorial : ℝ) * Real.sqrt Real.pi)
    (Filter.Eventually.of_forall fun x => Real.exp_pos _) (by fun_prop)
    hermiteNormalization_pos
    (fun m n => by
      simpa using integral_hermiteDilated_mul_gaussianWeight m n)
    (memLp_hermiteDilated_normalized 𝕜)
    (bareNormalizedLp_ortho_eq_bot (𝕜 := 𝕜) hermiteDilated (fun x => Real.exp (-x ^ 2))
      (fun n => (n.factorial : ℝ) * Real.sqrt Real.pi) degree_hermiteDilated
      hermiteNormalization_pos ⟨1, one_pos, integrable_exp_mul_abs_gaussianWeight 1⟩
      (memLp_hermiteDilated_normalized 𝕜))

/-- **The basis vectors are the Hermite functions.** Without this the construction would only
exhibit *some* Hilbert basis; here the `√w`-envelope of `Hₙ(x√2)/√cₙ` is identified with `ψₙ`. -/
theorem coe_hermiteHilbertBasis : ⇑(hermiteHilbertBasis 𝕜) = hermiteFunctionLp 𝕜 := by
  funext n
  have hwpos : ∀ᵐ x ∂(volume : Measure ℝ), 0 < Real.exp (-x ^ 2) :=
    Filter.Eventually.of_forall fun x => Real.exp_pos _
  have hwm : AEMeasurable (fun x : ℝ => Real.exp (-x ^ 2)) volume := by fun_prop
  -- `w > 0` makes `μ` absolutely continuous with respect to `w·μ`, so the `w·μ`-a.e.
  -- representative of the normalized family is also a `volume`-a.e. one.
  have hac : (volume : Measure ℝ)
      ≪ volume.withDensity fun x => ENNReal.ofReal (Real.exp (-x ^ 2)) :=
    withDensity_absolutelyContinuous' hwm.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact Real.exp_pos _)
  rw [hermiteHilbertBasis, coe_hilbertBasisOfOrthogonalSystem]
  refine Lp.ext ?_
  filter_upwards [weightL2Isometry_apply (𝕜 := 𝕜) volume (fun x => Real.exp (-x ^ 2)) hwpos hwm
      (bareNormalizedLp (𝕜 := 𝕜) (fun n x => (hermiteDilated n).eval x)
        (fun x => Real.exp (-x ^ 2)) (fun n => (n.factorial : ℝ) * Real.sqrt Real.pi)
        (memLp_hermiteDilated_normalized 𝕜) n),
    (coeFn_bareNormalizedLp (𝕜 := 𝕜) (fun n x => (hermiteDilated n).eval x)
      (fun x => Real.exp (-x ^ 2)) (fun n => (n.factorial : ℝ) * Real.sqrt Real.pi)
      (memLp_hermiteDilated_normalized 𝕜) n).filter_mono hac.ae_le,
    coeFn_hermiteFunctionLp (𝕜 := 𝕜) n] with x h1 h2 h3
  have hs : Real.sqrt (Real.exp (-x ^ 2)) = Real.exp (-(x ^ 2 / 2)) := by
    rw [show (-x ^ 2 : ℝ) = -(x ^ 2 / 2) + -(x ^ 2 / 2) by ring, Real.exp_add]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  rw [h1, h2, h3, hermiteFunction_def, eval_hermiteDilated, Algebra.smul_def, ← map_mul, hs]
  congr 1
  ring

end Basis

end TauCeti
