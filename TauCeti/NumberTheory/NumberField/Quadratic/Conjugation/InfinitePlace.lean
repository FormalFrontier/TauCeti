/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Basic
public import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# Quadratic conjugation and the real places

Let `K = ℚ(√d)` be a quadratic number field, presented by `θ : 𝓞 K` with `minpoly ℤ θ = X ^ 2 - d`
and `Algebra.adjoin ℚ {θ} = ⊤`, and let `σ = quadraticConj` be its nontrivial `ℚ`-automorphism. A
ring homomorphism `K →+* ℝ` is determined by the value it gives `θ`, and that value is one of the
two real square roots of `d`; so any two real embeddings of `K` either agree or differ by `σ`.

The arithmetic consequence recorded here is a **sign** statement: if `z / σz` is totally positive
then `z` and `σz` have the same sign at each real place, and since the real embeddings are `φ` and
`φ ∘ σ`, all real embeddings of `z` share one sign. Hence `z` or `-z` is totally positive, so the
principal ideal `(z)` has a totally positive generator.

This is the archimedean input to the *narrow* ambiguous class number formula: it is what replaces
the total-complexity hypothesis of the ordinary Hilbert-90 descent
(`NumberField.exists_map_ringOfIntegersQuadraticConj_eq_self_of_sq_eq_one`), where the sign of the
norm had to be controlled instead. Layer 3 of the multiquadratic roadmap needs the narrow class
group for real quadratic fields, where the ordinary descent fails.

## Main results

* `NumberField.realRingHom_eq_or_eq_comp_quadraticConj`: two real embeddings of a quadratic field
  either agree or differ by quadratic conjugation.
* `NumberField.isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj`:
  if `z / σ z` is totally positive then `z` or `-z` is totally positive.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The real embeddings of a quadratic field differ by conjugation.** Since `ρ θ` squares to the
rational `d` for every ring homomorphism `ρ : K →+* ℝ`, two of them send `θ` to the same square root
of `d` — in which case they agree — or to opposite ones, in which case one is the other precomposed
with quadratic conjugation. -/
theorem realRingHom_eq_or_eq_comp_quadraticConj (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (φ ψ : K →+* ℝ) :
    ψ = φ ∨ ∀ x : K, ψ x = φ (quadraticConj hmin hgen x) := by
  -- A ring homomorphism `K →+* ℝ` is a `ℚ`-algebra homomorphism, so `θ` generating `K` over `ℚ`
  -- means it is determined by the value it gives `θ`.
  have hdet : ∀ ρ₁ ρ₂ : K →+* ℝ, ρ₁ (θ : K) = ρ₂ (θ : K) → ρ₁ = ρ₂ := fun ρ₁ ρ₂ h => by
    have halg : ρ₁.toRatAlgHom = ρ₂.toRatAlgHom :=
      AlgHom.ext_of_adjoin_eq_top hgen (by rintro y rfl; exact h)
    exact RingHom.ext fun y => by simpa using AlgHom.congr_fun halg y
  have hsq : ∀ ρ : K →+* ℝ, ρ (θ : K) ^ 2 = ((d : ℚ) : ℝ) := fun ρ => by
    rw [← map_pow, coe_gen_sq_ratCast hmin, eq_ratCast (algebraMap ℚ K), map_ratCast]
  have hfac : (ψ (θ : K) - φ (θ : K)) * (ψ (θ : K) + φ (θ : K)) = 0 := by
    linear_combination hsq ψ - hsq φ
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (hdet _ _ (by linarith))
  · refine Or.inr fun x => ?_
    have hcomp : ψ = φ.comp ((quadraticConj hmin hgen).toAlgHom : K →ₐ[ℚ] K) := by
      refine hdet _ _ ?_
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom,
        AlgEquiv.toAlgHom_apply, quadraticConj_gen, map_neg]
      linarith
    exact congrFun (congrArg DFunLike.coe hcomp) x

/-- **A quotient by its conjugate that is totally positive forces a sign.** If `z / σ z` is totally
positive, then `z` and `σ z` have the same sign at each real place; since every
real embedding is either `φ` or `φ ∘ σ` for one fixed `φ`, all real embeddings of `z` have the same
sign, so `z` or `-z` is totally positive. Over a totally complex field both alternatives hold
vacuously. -/
theorem isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {z : K}
    (h : IsTotallyPositive (z / quadraticConj hmin hgen z)) :
    IsTotallyPositive z ∨ IsTotallyPositive (-z) := by
  by_cases hsome : ∃ w : InfinitePlace K, w.IsReal
  · obtain ⟨w₀, hw₀⟩ := hsome
    set φ₀ := embedding_of_isReal hw₀ with hφ₀
    -- At the chosen place the values of `z` and `σ z` have the same, nonzero, sign.
    have hsame : 0 < φ₀ z * φ₀ (quadraticConj hmin hgen z) := by
      have hdiv := isTotallyPositive_iff.mp h w₀ hw₀
      rw [map_div₀] at hdiv
      exact (div_pos_iff.mp hdiv).elim (fun hh => mul_pos hh.1 hh.2)
        fun hh => mul_pos_of_neg_of_neg hh.1 hh.2
    have hne : φ₀ z ≠ 0 := fun h0 => by rw [h0, zero_mul] at hsame; exact lt_irrefl 0 hsame
    -- Every real embedding is `φ₀` or `φ₀ ∘ σ`, so it gives `z` the sign that `φ₀` does.
    have hall : ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < φ₀ z * embedding_of_isReal hw z := by
      intro w hw
      rcases realRingHom_eq_or_eq_comp_quadraticConj hmin hgen φ₀ (embedding_of_isReal hw) with
        hcase | hcase
      · rw [hcase]; exact mul_self_pos.mpr hne
      · rw [hcase z]; exact hsame
    rcases hne.lt_or_gt with hlt | hgt
    · refine Or.inr (isTotallyPositive_iff.mpr fun w hw => ?_)
      rw [map_neg, neg_pos]
      nlinarith [hall w hw]
    · exact Or.inl (isTotallyPositive_iff.mpr fun w hw => by nlinarith [hall w hw])
  · exact Or.inl (isTotallyPositive_iff.mpr fun w hw => absurd ⟨w, hw⟩ hsome)

end NumberField
