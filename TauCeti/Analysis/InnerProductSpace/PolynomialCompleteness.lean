module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.InnerProductSpace.WeightedOrthogonalBasis
public import TauCeti.Probability.Moments.VanishingMoments
public import Mathlib.Algebra.Polynomial.Sequence

/-!
# Completeness of an orthogonal polynomial system from moment determinacy

`TauCeti.hilbertBasisOfWeightedMeasure` assembles a `HilbertBasis` of `L²(w·μ)` from an
orthogonality relation *and* a completeness hypothesis `(span …)ᗮ = ⊥`, but nothing in the library
discharges that hypothesis. This file supplies it for a family of polynomials of exact degree,
the case every classical orthogonal family falls under.

The mechanism is moment determinacy. If the weighted measure `w·μ` carries one finite
exponential moment then `TauCeti.ae_eq_zero_of_forall_moment_eq_zero_of_exists_integrable_exp`
says a `g ∈ L²(w·μ)` orthogonal to every *monomial* vanishes. So the only thing completeness needs
of the family is that it **spans `ℝ[X]`**, and that is the hypothesis the core theorem takes.

Exact degrees are one sufficient route to spanning, not the content of the argument: a family with
`(p n).degree = n` spans, because over a field every nonzero leading coefficient is a unit
(`Polynomial.Sequence.span`). That case is kept as a corollary, since it is the one every classical
orthogonal family satisfies. Requiring `degree` rather than `natDegree` matters there:
`natDegree 0 = 0` would admit `p 0 = 0`, which silently destroys the basis.

## Main statements

* `TauCeti.memLp_two_algebraMap_eval` — polynomials lie in `L²` of a measure carrying one finite
  exponential moment.
* `TauCeti.memLp_two_bareNormalized` — the normalized-family `MemLp` obligation, discharged from
  that same exponential moment so callers need not repeat it.
* `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot_of_span_eq_top` — the completeness input
  of the B2 bridge, from spanning alone.
* `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot` — its exact-degree specialization.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A measure carrying one finite exponential moment integrates every monomial squared: `xⁿ` lies
in `L²`, because `|x|ⁿ ≤ (n!/bⁿ)·e^{b|x|}` and `e^{b|x|}` is square-integrable.

The rate is existential, matching the convention of the B1 forms this feeds. The proof runs at
*half* the supplied rate: `e^{(a/2)|x|}` squares to the supplied `e^{a|x|}`, which is what makes
one moment enough. -/
theorem memLp_two_algebraMap_pow {ν : Measure ℝ}
    (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|)) ν) (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜 x) ^ n) 2 ν := by
  obtain ⟨a, ha, hexpa⟩ := hexp
  set b := a / 2 with hb
  have hbpos : (0 : ℝ) < b := by positivity
  have hexpmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (b * |x|)) ν :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  have hexp2 : MemLp (fun x : ℝ => Real.exp (b * |x|)) 2 ν := by
    refine (memLp_two_iff_integrable_sq hexpmeas).2 ?_
    have hfun : (fun x : ℝ => Real.exp (a * |x|))
        = fun x : ℝ => Real.exp (b * |x|) ^ 2 := by
      funext x
      rw [sq, ← Real.exp_add, hb]
      ring_nf
    exact hfun ▸ hexpa
  have hK : (0 : ℝ) < (Nat.factorial n : ℝ) / b ^ n := by
    have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    positivity
  refine MemLp.of_le (hexp2.const_mul ((Nat.factorial n : ℝ) / b ^ n)) ?_ ?_
  · exact ((RCLike.continuous_ofReal.comp continuous_id).pow n).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have h := pow_abs_le_factorial_div_pow_mul_exp hbpos n x
    have hE : (0 : ℝ) < Real.exp (b * |x|) := Real.exp_pos _
    rw [RCLike.algebraMap_eq_ofReal, norm_pow, RCLike.norm_ofReal, Real.norm_eq_abs,
      abs_mul, abs_of_pos hK, abs_of_pos hE]
    linarith

/-- Every polynomial lies in `L²` of a measure carrying one finite exponential moment. -/
theorem memLp_two_algebraMap_eval {ν : Measure ℝ}
    (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|)) ν)
    (q : Polynomial ℝ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x)) 2 ν := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    have : (fun x : ℝ => (algebraMap ℝ 𝕜) ((q + r).eval x))
        = (fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x))
          + fun x : ℝ => (algebraMap ℝ 𝕜) (r.eval x) := by
      funext x; simp [map_add]
    rw [this]
    exact hq.add hr
  | monomial n a =>
    have : (fun x : ℝ => (algebraMap ℝ 𝕜) ((monomial n a).eval x))
        = fun x : ℝ => (algebraMap ℝ 𝕜 a) * (algebraMap ℝ 𝕜 x) ^ n := by
      funext x
      simp [eval_monomial, map_mul, map_pow]
    rw [this]
    exact (memLp_two_algebraMap_pow (𝕜 := 𝕜) hexp n).const_mul _

/-- Dividing by a constant keeps a polynomial in `L²`: `q/r` is again the evaluation of a
polynomial, namely `C r⁻¹ * q`. This also covers `r = 0`, where both sides are `0`. -/
theorem memLp_two_algebraMap_eval_div {ν : Measure ℝ}
    (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|)) ν)
    (q : Polynomial ℝ) (r : ℝ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x / r)) 2 ν := by
  have hrw : (fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x / r))
      = fun x : ℝ => (algebraMap ℝ 𝕜) ((Polynomial.C r⁻¹ * q).eval x) := by
    funext x
    simp [div_eq_mul_inv, mul_comm]
  rw [hrw]
  exact memLp_two_algebraMap_eval (𝕜 := 𝕜) hexp _

/-- The `MemLp` obligation of `TauCeti.bareNormalizedLp` for a polynomial family, discharged from
the one exponential moment that the completeness theorem already assumes. Supplied as the default
value of that theorem's `hmem` argument, so callers do not repeat this proof. -/
theorem memLp_two_bareNormalized {ν : Measure ℝ}
    (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|)) ν)
    (p : ℕ → Polynomial ℝ) (c : ℕ → ℝ) (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n))) 2 ν :=
  memLp_two_algebraMap_eval_div (𝕜 := 𝕜) hexp (p n) _

/-- **Roadmap B1 → B2 bridge: completeness of a spanning polynomial family.**

If the weighted measure `w·μ` carries one finite exponential moment and `p` spans `ℝ[X]`, then the
normalized polynomials span a dense subspace of `L²(w·μ)` — the orthogonal complement of their span
is trivial. This is the `hcomplete` input that `TauCeti.hilbertBasisOfWeightedMeasure` consumes.

Spanning is all the argument uses; see
`TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot` for the exact-degree families that motivate
it. -/
theorem orthogonal_span_range_bareNormalizedLp_eq_bot_of_span_eq_top {μ : Measure ℝ}
    (p : ℕ → Polynomial ℝ) (w : ℝ → ℝ) (c : ℕ → ℝ)
    (hspan : Submodule.span ℝ (Set.range p) = ⊤) (hc : ∀ n, 0 < c n)
    (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|))
      (μ.withDensity fun x => ENNReal.ofReal (w x)))
    (hmem : ∀ n, MemLp (fun x => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity fun x => ENNReal.ofReal (w x)) :=
      fun n => memLp_two_bareNormalized (𝕜 := 𝕜) hexp p c n) :
    (Submodule.span 𝕜 (Set.range
      (bareNormalizedLp (𝕜 := 𝕜) (fun n x => (p n).eval x) w c hmem)))ᗮ = ⊥ := by
  set ν : Measure ℝ := μ.withDensity (fun x => ENNReal.ofReal (w x)) with hνdef
  rw [Submodule.eq_bot_iff]
  intro G hG
  -- Integrability of `q · G` for every polynomial `q`, by Cauchy–Schwarz.
  have hGmem : MemLp (⇑G) 2 ν := Lp.memLp G
  have hint : ∀ q : Polynomial ℝ,
      Integrable (fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x) * G x) ν := fun q => by
    simpa only [Pi.mul_def] using
      (memLp_two_algebraMap_eval (𝕜 := 𝕜) hexp q).integrable_mul hGmem
  -- `G` is orthogonal to each member of the family, hence to each `p n` after clearing `√cₙ`.
  have hfam : ∀ n : ℕ, ∫ x, (algebraMap ℝ 𝕜) ((p n).eval x) * G x ∂ν = 0 := by
    intro n
    have hmemspan : bareNormalizedLp (𝕜 := 𝕜) (fun n x => (p n).eval x) w c hmem n
        ∈ Submodule.span 𝕜 (Set.range
          (bareNormalizedLp (𝕜 := 𝕜) (fun n x => (p n).eval x) w c hmem)) :=
      Submodule.subset_span ⟨n, rfl⟩
    have h0 := (Submodule.mem_orthogonal _ _).mp hG _ hmemspan
    rw [MeasureTheory.L2.inner_def] at h0
    -- The `Lp` representative is a real cast, so the conjugation in `⟪·,·⟫` is the identity.
    have h1 : ∫ x, (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n)) * G x ∂ν = 0 := by
      rw [← h0]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_bareNormalizedLp (𝕜 := 𝕜) (fun n x => (p n).eval x) w c hmem n]
        with x hx
      rw [hx, RCLike.inner_apply, RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal]
      exact mul_comm _ _
    have hs : Real.sqrt (c n) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hc n))
    have h2 : ∀ x : ℝ, (algebraMap ℝ 𝕜) ((p n).eval x) * G x
        = (algebraMap ℝ 𝕜 (Real.sqrt (c n)))
          * ((algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n)) * G x) := by
      intro x
      rw [← mul_assoc, ← map_mul]
      congr 2
      field_simp
    simp_rw [h2]
    rw [integral_const_mul, h1, mul_zero]
  -- Transfer to every polynomial through the degree filtration.
  have hpoly : ∀ q : Polynomial ℝ, ∫ x, (algebraMap ℝ 𝕜) (q.eval x) * G x ∂ν = 0 := by
    intro q
    have hq : q ∈ Submodule.span ℝ (Set.range p) := hspan ▸ Submodule.mem_top
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨n, rfl⟩ := hq
      exact hfam n
    | zero => simp
    | add a b _ _ ha hb =>
      have hadd : ∫ x, (algebraMap ℝ 𝕜) ((a + b).eval x) * G x ∂ν
          = (∫ x, (algebraMap ℝ 𝕜) (a.eval x) * G x ∂ν)
            + ∫ x, (algebraMap ℝ 𝕜) (b.eval x) * G x ∂ν := by
        rw [← integral_add (hint a) (hint b)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [map_add, add_mul]
      rw [hadd, ha, hb, add_zero]
    | smul r a _ ha =>
      have hsmul : ∫ x, (algebraMap ℝ 𝕜) ((r • a).eval x) * G x ∂ν
          = (algebraMap ℝ 𝕜 r) * ∫ x, (algebraMap ℝ 𝕜) (a.eval x) * G x ∂ν := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp [Polynomial.eval_smul, smul_eq_mul, map_mul, mul_assoc]
      rw [hsmul, ha, mul_zero]
  -- In particular every monomial moment vanishes, so moment determinacy applies.
  have hmom : ∀ n : ℕ, ∫ x, (algebraMap ℝ 𝕜 x) ^ n * G x ∂ν = 0 := by
    intro n
    have h := hpoly (Polynomial.X ^ n)
    simpa [eval_pow, eval_X, map_pow] using h
  have := ae_eq_zero_of_forall_moment_eq_zero_of_exists_integrable_exp hexp hGmem hmom
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr this

/-- **Completeness of an exact-degree polynomial family** — the specialization of
`TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot_of_span_eq_top` that every classical
orthogonal family satisfies.

Exact degrees make `p` a `Polynomial.Sequence`, and over a field every nonzero leading coefficient
is a unit, so `p` spans `ℝ[X]`. -/
theorem orthogonal_span_range_bareNormalizedLp_eq_bot {μ : Measure ℝ}
    (p : ℕ → Polynomial ℝ) (w : ℝ → ℝ) (c : ℕ → ℝ)
    (hdeg : ∀ n, (p n).degree = (n : WithBot ℕ)) (hc : ∀ n, 0 < c n)
    (hexp : ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|))
      (μ.withDensity fun x => ENNReal.ofReal (w x)))
    (hmem : ∀ n, MemLp (fun x => (algebraMap ℝ 𝕜) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity fun x => ENNReal.ofReal (w x)) :=
      fun n => memLp_two_bareNormalized (𝕜 := 𝕜) hexp p c n) :
    (Submodule.span 𝕜 (Set.range
      (bareNormalizedLp (𝕜 := 𝕜) (fun n x => (p n).eval x) w c hmem)))ᗮ = ⊥ :=
  orthogonal_span_range_bareNormalizedLp_eq_bot_of_span_eq_top p w c
    (Polynomial.Sequence.span (⟨p, hdeg⟩ : Polynomial.Sequence ℝ) fun i =>
      isUnit_iff_ne_zero.mpr <| Polynomial.leadingCoeff_ne_zero.mpr <|
        Polynomial.Sequence.ne_zero (⟨p, hdeg⟩ : Polynomial.Sequence ℝ) i)
    hc hexp hmem

end TauCeti
