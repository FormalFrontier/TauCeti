module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Probability.Moments.Determinacy
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Vanishing moments force a function to be zero (measure level)

The measure-level instance of roadmap milestone **B1** of the `OrthogonalL2Bases` roadmap.
`TauCeti.ae_eq_zero_of_forall_moment_eq_zero` handles a real function whose *exponentially
weighted* products are integrable; this restates it in the form the completeness step actually
consumes — a scalar-valued `g ∈ L²(ν)` against a measure `ν` all of whose exponential moments
are finite.

The two hypotheses trade places: instead of assuming `e^{a|x|} · g` integrable for every `a`, we
assume it of the *measure* (`e^{a|x|} ∈ L¹(ν)`) and of `g` only that it lies in `L²(ν)`. Cauchy–
Schwarz bridges the two, which is what makes this the usable form: `hexp` becomes a statement
about the weight alone (Gaussian decay, or automatic for compact support), independent of `g`.
-/

public section

namespace TauCeti

open MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Roadmap B1, measure level.** A measure `ν` on `ℝ` with every exponential moment finite is
moment-determinate, so a `g ∈ L²(ν)` orthogonal to every monomial is a.e. `0`.

Finiteness of `ν` is not a separate hypothesis: it is the `a = 0` case of `hexp`. -/
theorem ae_eq_zero_of_forall_moment_eq_zero_of_finite_expMoments
    {ν : Measure ℝ}
    (hexp : ∀ a : ℝ, 0 ≤ a → Integrable (fun x : ℝ => Real.exp (a * |x|)) ν)
    {g : ℝ → 𝕜} (hg : MemLp g 2 ν)
    (hmom : ∀ n : ℕ, ∫ x, (algebraMap ℝ 𝕜 x) ^ n * g x ∂ν = 0) :
    g =ᵐ[ν] 0 := by
  -- `a = 0` makes `hexp` say `Integrable (fun _ => 1) ν`, i.e. `ν` is finite.
  haveI hnu : IsFiniteMeasure ν := by
    have h := hexp 0 le_rfl
    simp only [zero_mul, Real.exp_zero] at h
    exact (integrable_const_iff.mp h).resolve_left one_ne_zero
  have hexpmeas : ∀ a : ℝ, AEStronglyMeasurable (fun x : ℝ => Real.exp (a * |x|)) ν :=
    fun a => (Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).aestronglyMeasurable
  -- The weight is itself square-integrable, because `hexp` is available at `2a` as well.
  have hexp2 : ∀ a : ℝ, 0 ≤ a → MemLp (fun x : ℝ => Real.exp (a * |x|)) 2 ν := by
    intro a ha
    refine (memLp_two_iff_integrable_sq (hexpmeas a)).2 ?_
    have h := hexp (2 * a) (by positivity)
    have hfun : (fun x : ℝ => Real.exp (2 * a * |x|))
        = fun x : ℝ => Real.exp (a * |x|) ^ 2 := by
      funext x
      rw [sq, ← Real.exp_add]
      ring_nf
    exact hfun ▸ h
  -- Cauchy–Schwarz: an `L²` function against the `L²` weight is integrable.
  have key : ∀ f : ℝ → ℝ, MemLp f 2 ν → ∀ a : ℝ, 0 ≤ a →
      Integrable (fun x : ℝ => Real.exp (a * |x|) * f x) ν := by
    intro f hf a ha
    simpa only [Pi.mul_def] using (hexp2 a ha).integrable_mul hf
  -- Monomials are square-integrable: `|x|ⁿ ≤ n! · e^{|x|}` and the right side is in `L²`.
  have hpolyL2 : ∀ n : ℕ, MemLp (fun x : ℝ => (algebraMap ℝ 𝕜 x) ^ n) 2 ν := by
    intro n
    refine MemLp.of_le ((hexp2 1 zero_le_one).const_mul (Nat.factorial n : ℝ)) ?_ ?_
    · exact ((RCLike.continuous_ofReal.comp continuous_id).pow n).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n
      rw [div_le_iff₀ hfac] at h
      have hE : (0 : ℝ) < Real.exp (1 * |x|) := Real.exp_pos _
      rw [RCLike.algebraMap_eq_ofReal, norm_pow, RCLike.norm_ofReal, Real.norm_eq_abs,
        abs_mul, abs_of_pos hfac, abs_of_pos hE, one_mul]
      linarith
  -- Hence each monomial moment integrand is integrable, so `re`/`im` pass through the integral.
  have hint : ∀ n : ℕ, Integrable (fun x : ℝ => (algebraMap ℝ 𝕜 x) ^ n * g x) ν :=
    fun n => by simpa only [Pi.mul_def] using (hpolyL2 n).integrable_mul hg
  have hsplit : ∀ (x : ℝ) (n : ℕ),
      (algebraMap ℝ 𝕜 x) ^ n * g x = ((x ^ n : ℝ) : 𝕜) * g x := by
    intro x n
    rw [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_pow]
  -- Monomials are real, so real and imaginary parts each inherit vanishing moments.
  have hre : ∀ n : ℕ, ∫ x, x ^ n * RCLike.re (g x) ∂ν = 0 := by
    intro n
    have h0 : RCLike.re (∫ x, (algebraMap ℝ 𝕜 x) ^ n * g x ∂ν) = 0 := by
      rw [hmom n]; simp
    rw [← integral_re (hint n)] at h0
    have hfun : (fun x : ℝ => x ^ n * RCLike.re (g x))
        = fun x : ℝ => RCLike.re ((algebraMap ℝ 𝕜 x) ^ n * g x) := by
      funext x
      rw [hsplit x n, RCLike.re_ofReal_mul]
    rw [hfun]
    exact h0
  have him : ∀ n : ℕ, ∫ x, x ^ n * RCLike.im (g x) ∂ν = 0 := by
    intro n
    have h0 : RCLike.im (∫ x, (algebraMap ℝ 𝕜 x) ^ n * g x ∂ν) = 0 := by
      rw [hmom n]; simp
    rw [← integral_im (hint n)] at h0
    have hfun : (fun x : ℝ => x ^ n * RCLike.im (g x))
        = fun x : ℝ => RCLike.im ((algebraMap ℝ 𝕜 x) ^ n * g x) := by
      funext x
      rw [hsplit x n, RCLike.im_ofReal_mul]
    rw [hfun]
    exact h0
  -- Apply the weighted-product form of B1 to the real and imaginary parts separately.
  have hzre := ae_eq_zero_of_forall_moment_eq_zero (ν := ν) _ (key _ hg.re) hre
  have hzim := ae_eq_zero_of_forall_moment_eq_zero (ν := ν) _ (key _ hg.im) him
  filter_upwards [hzre, hzim] with x hx1 hx2
  simp only [Pi.zero_apply] at hx1 hx2 ⊢
  exact RCLike.ext (by simp [hx1]) (by simp [hx2])

end TauCeti
