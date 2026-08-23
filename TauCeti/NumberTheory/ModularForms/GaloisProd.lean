/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
public import TauCeti.NumberTheory.ModularForms.QExpansion.Order

/-!
# The Galois product of a periodic function

For `f : ℍ → α` valued in a commutative monoid and `N : ℕ`, the product
`galoisProd N f τ = ∏_{j < N} f(τ − j)` over the integer translates — the building block
of the modular norm map. If `f` has period `N` along `ofComplex` then the product has
period `1`. A product of functions bounded at `i∞` is bounded at `i∞` over any seminormed
commutative ring, and for complex-valued holomorphic `f` the product is holomorphic; when
moreover `0 < N`, `f` is bounded and holomorphic, the `q`-expansion of the product at
period `1` has the same order at `0` as that of `f` at period `N`.

## Main declarations

* `TauCeti.ModularForm.galoisProd`.
* `TauCeti.ModularForm.qExpansion_one_galoisProd_order_eq`.

## References

* [Mathlib PR #39086](https://github.com/leanprover-community/mathlib4/pull/39086)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane Complex Function SlashInvariantForm Periodic
open TauCeti.UpperHalfPlane

open scoped ModularForm Topology Filter Manifold

namespace TauCeti

namespace ModularForm

section GaloisProd
variable {α : Type*} [CommMonoid α] (N : ℕ) (f : ℍ → α)
/-- The product `∏_{j < N} f(τ - j)`, used as a building block of the norm map. -/
noncomputable def galoisProd (τ : ℍ) : α :=
  ∏ j ∈ Finset.range N, f (ofComplex ((τ : ℂ) - j))
variable {N f}
@[simp]
lemma galoisProd_apply (τ : ℍ) :
    galoisProd N f τ = ∏ j ∈ Finset.range N, f (ofComplex ((τ : ℂ) - j)) := by
  -- `galoisProd` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change ∏ j ∈ Finset.range N, f (ofComplex ((τ : ℂ) - j)) = _
  rfl
/-- If `f` has period `N` along `ofComplex`, then `galoisProd N f` has period `1`. -/
lemma galoisProd_periodic_one
    (hf_per : Function.Periodic (f ∘ ofComplex) (N : ℝ)) :
    Function.Periodic (galoisProd N f ∘ ofComplex) 1 := by
  refine periodic_comp_ofComplex_iff.mpr fun τ ↦ ?_
  simp only [galoisProd_apply, coe_vadd, Complex.ofReal_one]
  -- For `N = 0` both sides are the empty product; otherwise peel the last factor.
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by lia⟩
  rw [Finset.prod_range_succ' (fun j ↦ f (ofComplex (1 + ↑τ - ↑j))),
    Finset.prod_range_succ (fun j ↦ f (ofComplex (↑τ - ↑j)))]
  have hinner : ∏ j ∈ Finset.range n, f (ofComplex (1 + ↑τ - ↑(j + 1))) =
      ∏ j ∈ Finset.range n, f (ofComplex ((τ : ℂ) - ↑j)) :=
    Finset.prod_congr rfl fun j _ ↦ by
      congr 2
      push_cast
      ring
  have hbdry : f (ofComplex (1 + ↑τ - ↑(0 : ℕ))) = f (ofComplex ((τ : ℂ) - ↑n)) := by
    -- Rewrite the boundary point so the period hypothesis applies verbatim.
    rw [show 1 + (τ : ℂ) - ↑(0 : ℕ) = ((τ : ℂ) - ↑n) + ↑(n + 1 : ℕ) by push_cast; ring]
    exact hf_per ((τ : ℂ) - ↑n)
  rw [hinner, hbdry]

end GaloisProd
section GaloisProdComplex
variable {N : ℕ} {f : ℍ → ℂ}
/-- If `f` is holomorphic on `ℍ`, so is `galoisProd N f`. -/
lemma mdifferentiable_galoisProd (hf_mdiff : MDiff f) : MDiff (galoisProd N f) := by
  unfold galoisProd
  have hfo : DifferentiableOn ℂ (f ∘ ofComplex) {z | 0 < z.im} :=
    mdifferentiable_iff.mp hf_mdiff
  intro τ
  rw [mdifferentiableAt_iff]
  have hτj : ∀ j : ℕ, 0 < ((τ : ℂ) - ↑j).im := fun j ↦ by
    simp [Complex.sub_im, Complex.natCast_im, τ.im_pos]
  refine DifferentiableAt.fun_finsetProd fun j _ ↦
    DifferentiableAt.congr_of_eventuallyEq
      (((hfo ((τ : ℂ) - j) (hτj j)).differentiableAt
        (isOpen_upperHalfPlaneSet.mem_nhds (hτj j))).comp (τ : ℂ)
        ((differentiableAt_id (𝕜 := ℂ)).sub (differentiableAt_const (c := (j : ℂ))))) ?_
  filter_upwards [eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  simp only [Function.comp_apply, id_eq, Pi.sub_apply] at hz ⊢
  rw [hz]
/-- If `f` is bounded at `i∞`, so is `galoisProd N f`, over any seminormed commutative
ring. -/
lemma isBoundedAtImInfty_galoisProd {R : Type*} [SeminormedCommRing R] {N : ℕ} {f : ℍ → R}
    (hf_bdd : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (galoisProd N f) := by
  unfold galoisProd IsBoundedAtImInfty Filter.BoundedAtFilter
  rw [← Finset.prod_fn]
  refine Filter.BoundedAtFilter.prod _ fun j _ ↦ hf_bdd.comp_tendsto ?_
  simp only [atImInfty, Filter.tendsto_comap_iff, Function.comp_def]
  refine Filter.tendsto_comap.congr' (.of_forall fun τ ↦ ?_)
  have him : 0 < ((τ : ℂ) - ↑j).im := by
    simp [Complex.sub_im, Complex.natCast_im, τ.im_pos]
  simp [ofComplex_apply_of_im_pos him]
/-- Each rotated factor of the cusp function at period `N` is the value of `f` at the
corresponding integer translate of the preimage point. -/
private lemma cuspFunction_factor_eq (hNR_ne : (N : ℝ) ≠ 0)
    (hf_per : Function.Periodic (f ∘ ofComplex) (N : ℝ)) {q : ℂ} {τ : ℍ}
    (hτq : Function.Periodic.qParam (N : ℝ) τ = q) (j : ℕ) :
    cuspFunction (N : ℝ) f (q * Complex.exp (-2 * Real.pi * Complex.I * j / N)) =
      f (ofComplex ((τ : ℂ) - j)) := by
  have him : 0 < ((τ : ℂ) - ↑j).im := by
    simp [Complex.sub_im, Complex.natCast_im, τ.im_pos]
  have hqj : q * Complex.exp (-2 * Real.pi * Complex.I * j / N) =
      Function.Periodic.qParam (N : ℝ) ((⟨(τ : ℂ) - j, him⟩ : ℍ) : ℂ) := by
    -- Align the two coercion routes `ℕ → ℂ` and `ℕ → ℝ → ℂ` before rewriting.
    rw [show ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) by push_cast; rfl, ← hτq,
      ← TauCeti.Periodic.qParam_sub (h := (N : ℝ)) τ j]
  rw [hqj, eq_cuspFunction ⟨(τ : ℂ) - j, him⟩ hNR_ne hf_per, ofComplex_apply_of_im_pos him]

private lemma cuspFunction_one_galoisProd_pow_eq (hN : 0 < N)
    (hf_per : Function.Periodic (f ∘ ofComplex) (N : ℝ))
    (hf_bdd : IsBoundedAtImInfty f) (hf_mdiff : MDiff f) :
    (fun q : ℂ ↦ cuspFunction 1 (galoisProd N f) (q ^ N)) =ᶠ[𝓝 0]
      fun q : ℂ ↦ ∏ j ∈ Finset.range N,
        cuspFunction (N : ℝ) f (q * Complex.exp (-2 * Real.pi * Complex.I * j / N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNR_ne : (N : ℝ) ≠ 0 := hNR.ne'
  have hRHS_an : AnalyticAt ℂ (cuspFunction (N : ℝ) f) 0 :=
    analyticAt_cuspFunction_zero hNR hf_per hf_mdiff hf_bdd
  have hLHS_cts : ContinuousAt (fun q : ℂ ↦ cuspFunction 1 (galoisProd N f) (q ^ N)) 0 :=
    (analyticAt_cuspFunction_zero one_pos (galoisProd_periodic_one hf_per)
      (mdifferentiable_galoisProd hf_mdiff)
      (isBoundedAtImInfty_galoisProd hf_bdd)).continuousAt.comp_of_eq
      (by fun_prop) (by simp [zero_pow hN.ne'])
  have hRHS_cts : ContinuousAt (fun q : ℂ ↦ ∏ j ∈ Finset.range N,
      cuspFunction (N : ℝ) f (q * Complex.exp (-2 * Real.pi * Complex.I * j / N))) 0 :=
    tendsto_finsetProd _ fun j _ ↦
      (hRHS_an.continuousAt.comp_of_eq (by fun_prop) (by simp)).tendsto
  rw [← hLHS_cts.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hRHS_cts,
    eventuallyEq_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq_lt hq_ne
  rw [mem_ball_zero_iff] at hq_lt
  set τ : ℍ := ⟨Function.Periodic.invQParam (N : ℝ) q,
    Function.Periodic.im_invQParam_pos_of_norm_lt_one hNR hq_lt hq_ne⟩
  have hτq : Function.Periodic.qParam (N : ℝ) τ = q :=
    Function.Periodic.qParam_right_inv hNR_ne hq_ne
  have hqN : q ^ N = Function.Periodic.qParam 1 (τ : ℂ) := by
    rw [← hτq, ← mul_one (N : ℝ), TauCeti.Periodic.qParam_nat_mul_pow hN.ne']
  rw [hqN, eq_cuspFunction τ one_ne_zero (galoisProd_periodic_one hf_per), galoisProd_apply]
  exact Finset.prod_congr rfl fun j _ ↦ (cuspFunction_factor_eq hNR_ne hf_per hτq j).symm
/-- Precomposing with a rotation does not change the analytic order at `0`. -/
private lemma analyticOrderAt_factor_eq (j : ℕ) :
    analyticOrderAt (fun q : ℂ ↦ cuspFunction (N : ℝ) f
      (q * Complex.exp (-2 * Real.pi * Complex.I * j / N))) 0 =
      analyticOrderAt (cuspFunction (N : ℝ) f) 0 := by
  rw [← Function.comp_def, analyticOrderAt_comp_of_deriv_ne_zero
    (f := cuspFunction (N : ℝ) f) (by fun_prop) (by simp [Complex.exp_ne_zero]), zero_mul]

/-- The `q`-expansion of `galoisProd N f` (period `1`) and that of `f` (period `N`) have the same
order at `0`. -/
lemma qExpansion_one_galoisProd_order_eq (hN : 0 < N)
    (hf_per : Function.Periodic (f ∘ ofComplex) (N : ℝ))
    (hf_bdd : IsBoundedAtImInfty f) (hf_mdiff : MDiff f) :
    (qExpansion 1 (galoisProd N f)).order = (qExpansion (N : ℝ) f).order := by
  have hLHS_an : AnalyticAt ℂ (cuspFunction 1 (galoisProd N f)) 0 :=
    analyticAt_cuspFunction_zero one_pos (galoisProd_periodic_one hf_per)
      (mdifferentiable_galoisProd hf_mdiff) (isBoundedAtImInfty_galoisProd hf_bdd)
  have hRHS_an : AnalyticAt ℂ (cuspFunction (N : ℝ) f) 0 :=
    analyticAt_cuspFunction_zero (mod_cast hN) hf_per hf_mdiff hf_bdd
  rw [qExpansion_order_eq_analyticOrderAt_cuspFunction hLHS_an,
    qExpansion_order_eq_analyticOrderAt_cuspFunction hRHS_an]
  set ML := analyticOrderAt (cuspFunction 1 (galoisProd N f)) 0
  set MR := analyticOrderAt (cuspFunction (N : ℝ) f) 0
  have h_factor_an : ∀ j ∈ Finset.range N,
      AnalyticAt ℂ (fun q : ℂ ↦ cuspFunction (N : ℝ) f
        (q * Complex.exp (-2 * Real.pi * Complex.I * j / N))) 0 := fun j _ ↦
    hRHS_an.comp_of_eq (by fun_prop) (by simp)
  have h_factor_order : ∀ j ∈ Finset.range N,
      analyticOrderAt (fun q : ℂ ↦ cuspFunction (N : ℝ) f
        (q * Complex.exp (-2 * Real.pi * Complex.I * j / N))) 0 = MR := fun j _ ↦
    analyticOrderAt_factor_eq j
  have h_combine : ML * (N : ℕ∞) = (N : ℕ∞) * MR := by
    rw [← analyticOrderAt_comp_pow_zero hLHS_an hN,
      analyticOrderAt_congr (cuspFunction_one_galoisProd_pow_eq hN hf_per hf_bdd hf_mdiff),
      ← Finset.prod_fn, analyticOrderAt_prod h_factor_an,
      Finset.sum_congr rfl h_factor_order, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hN0 : (N : ℕ∞) ≠ 0 := mod_cast hN.ne'
  exact (WithTop.mul_right_strictMono (pos_iff_ne_zero.mpr hN0) (ENat.natCast_ne_top N)).injective
    (mul_comm ML _ ▸ h_combine)
end GaloisProdComplex

end ModularForm

end TauCeti

end
