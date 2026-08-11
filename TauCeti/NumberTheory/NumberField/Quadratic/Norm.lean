/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.Basic
public import TauCeti.RingTheory.Norm.Quadratic

/-!
# The field norm on a quadratic number field

For a quadratic number field `K = ℚ(√d)` presented by an algebraic integer `θ : 𝓞 K` generating
`K` over `ℚ` with `minpoly ℤ θ = X² - d`, this file computes the field norm `Algebra.norm ℚ` on
`K` in terms of the coordinates in the power basis `1, θ`:

* `norm_gen`: the norm of the generator is the radicand, `N(θ) = -d`;
* `exists_eq_add_mul_gen`: every element of `K` is `b + aθ` for rationals `a, b`;
* `norm_add_mul_gen`: in those coordinates the norm is `N(b + aθ) = b² - d·a²`;
* `norm_pos_of_radicand_neg`: when `d < 0` — the imaginary quadratic case, where `K` is totally
  complex — the norm is strictly positive on every nonzero element.

The positivity is a descent input for the genus theory of the multiquadratic roadmap: for a
norm-one element `α` it upgrades `N(α) = ±1` to `N(α) = 1`, the hypothesis of Hilbert's
Theorem 90 used to realise a `2`-torsion class by an ambiguous ideal.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*.
-/

public section

open Polynomial NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- The `ℚ`-power basis `1, θ` of the quadratic field `K = ℚ(θ)`. -/
private noncomputable def genPowerBasis (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : PowerBasis ℚ K :=
  PowerBasis.ofAdjoinEqTop' θ.isIntegral_coe.tower_top hgen

private theorem genPowerBasis_gen (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (genPowerBasis hgen).gen = (θ : K) :=
  PowerBasis.ofAdjoinEqTop'_gen _ hgen

private theorem genPowerBasis_dim (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : (genPowerBasis hgen).dim = 2 := by
  rw [← (genPowerBasis hgen).natDegree_minpoly, genPowerBasis_gen, minpoly_rat_quadratic hmin,
    natDegree_X_pow_sub_C]

/-- **The norm of the generator is the radicand:** `N(θ) = -d`. This is the constant coefficient of
the minimal polynomial `X² - d` (up to the sign `(-1)^{[K:ℚ]}`, here `+1`). -/
theorem norm_gen (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.norm ℚ (θ : K) = -(d : ℚ) := by
  rw [← genPowerBasis_gen hgen, (genPowerBasis hgen).norm_gen_eq_coeff_zero_minpoly,
    genPowerBasis_dim hmin hgen, genPowerBasis_gen, minpoly_rat_quadratic hmin]
  simp [coeff_sub, coeff_X_pow, coeff_C]

/-- **Every element of a quadratic field is `b + aθ`** for rationals `a, b`: the power basis `1, θ`
spans `K` over `ℚ`, and any polynomial in `θ` reduces modulo the degree-two minimal polynomial. -/
theorem exists_eq_add_mul_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (x : K) :
    ∃ a b : ℚ, x = algebraMap ℚ K b + algebraMap ℚ K a * (θ : K) := by
  obtain ⟨f, hf, rfl⟩ := (genPowerBasis hgen).exists_eq_aeval x
  rw [genPowerBasis_dim hmin hgen] at hf
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one (by omega : f.natDegree ≤ 1)
  refine ⟨a, b, ?_⟩
  rw [genPowerBasis_gen]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  ring

/-- **The norm in power-basis coordinates:** `N(b + aθ) = b² - d·a²`. Specialises the generic
quadratic norm formula `b² + ab·Tr(θ) + a²·N(θ)` to `Tr(θ) = 0` and `N(θ) = -d`. -/
theorem norm_add_mul_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (a b : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ K b + algebraMap ℚ K a * (θ : K)) = b ^ 2 - (d : ℚ) * a ^ 2 := by
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨finrank_rat_eq_two hmin hgen⟩
  rw [Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul, trace_gen_eq_zero hmin,
    norm_gen hmin hgen]
  ring

/-- **The norm is positive in the imaginary case.** When `d < 0` the field `K = ℚ(√d)` is totally
complex, and `N(b + aθ) = b² + |d|·a²`, so the norm is strictly positive on every nonzero element.
This is the sign input that turns a norm-`±1` element into a norm-`1` one for Hilbert 90. -/
theorem norm_pos_of_radicand_neg (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd : d < 0) {x : K} (hx : x ≠ 0) :
    0 < Algebra.norm ℚ x := by
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_gen hmin hgen x
  rw [norm_add_mul_gen hmin hgen]
  have hdq : (d : ℚ) < 0 := by exact_mod_cast hd
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (by rw [h.1, h.2]; simp)
  rcases hab with ha | hb
  · nlinarith [mul_self_pos.mpr ha, sq_nonneg b, sq_nonneg a]
  · nlinarith [mul_self_pos.mpr hb, sq_nonneg a, sq_nonneg b]

end TauCeti.NumberField
