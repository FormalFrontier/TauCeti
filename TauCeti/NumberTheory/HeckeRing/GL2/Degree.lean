/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.Degree
public import TauCeti.NumberTheory.HeckeRing.GL2.Basic
public import TauCeti.NumberTheory.HeckeRing.GL2.DiagonalCosetDegree
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Degrees of the `GL₂` Hecke operators

Shimura's Theorem 3.24, identities (6) and (7): the double coset of `diag(pⁱ, pⁱ⁺ᵏ)` has
degree `pᵏ⁻¹(p + 1)` for `k > 0`, and the degrees of the summed operators `T(m)` assemble
into the divisor-sum function, `deg T(m) = σ₁(m)`.

The prime-power case is a two-step induction on `k`. Expanding `T(pᵏ)` into its diagonal
terms `T(pⁱ, pᵏ⁻ⁱ)`, raising `k` by two shifts the indexing by one place and leaves every
term's degree unchanged, so only the new leading term `T(1, pᵏ⁺²)` contributes and
`deg T(pᵏ⁺²) = deg T(pᵏ) + pᵏ⁺¹(p + 1)`. Multiplicativity of `T` in coprime arguments then
upgrades the prime-power formula to every `m`.

## Main results

* `HeckeRing.GL2.degree_diagCoset_prime_pow`: `deg T(pⁱ, pⁱ⁺ᵏ) = pᵏ⁻¹(p + 1)` for `k > 0`.
* `HeckeRing.GL2.deg_heckeT_prime_pow`: `deg T(pᵏ) = 1 + p + ⋯ + pᵏ`.
* `HeckeRing.GL2.deg_heckeT`: `deg T(m) = σ₁(m)`.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Degree.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>).

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Theorem 3.24.
-/

public section

open Matrix HeckeRing HeckeRing.GLn LeftCosetModule

open scoped ArithmeticFunction.sigma

namespace HeckeRing.GL2

variable (p : ℕ)

/-- **The prime-power coset degree** (Shimura, Theorem 3.24(6)):
`deg T(pⁱ, pⁱ⁺ᵏ) = pᵏ⁻¹(p + 1)` for `k > 0`. -/
theorem degree_diagCoset_prime_pow (hp : p.Prime) (i k : ℕ) (hk : 0 < k) :
    (diagCoset ![p ^ i, p ^ (i + k)]).degree = p ^ (k - 1) * (p + 1) :=
  degree_diagCoset_of_ratio_eq_prime_pow p hp _
    (isDvdChain_iff.mpr fun j₁ j₂ h ↦ by
      fin_cases j₁ <;> fin_cases j₂ <;>
        simp_all [Nat.pow_dvd_pow p (Nat.le_add_right i k)])
    k hk (by simp [Nat.pow_div (Nat.le_add_right i k) hp.pos])

/-- The degree of a nonzero diagonal operator is the degree of its double coset. -/
private lemma deg_heckeTDiag_eq_diagCoset_degree {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hdvd : a ∣ d) :
    deg (posDetInt 2) (SLnZ 2) ℤ (heckeTDiag a d) = ((diagCoset ![a, d]).degree : ℤ) := by
  rw [heckeTDiag_eq_diagElem ha hd hdvd, diagElem_def, deg_single, nsmul_eq_mul, mul_one]

/-- A term of the `T(pᵏ)` expansion strictly below the middle has degree
`p^(k - 2i - 1)(p + 1)`. -/
private lemma deg_prime_pow_term_lt (hp : p.Prime) (i k : ℕ) (h2i : 2 * i < k) :
    deg (posDetInt 2) (SLnZ 2) ℤ (heckeTDiag (p ^ i) (p ^ (k - i))) =
      ((p ^ (k - 2 * i - 1) * (p + 1) : ℕ) : ℤ) := by
  -- `degree_diagCoset_prime_pow` is stated at `![p ^ i, p ^ (i + k')]`. Truncated ℕ-subtraction
  -- hides that shape inside `k - i`, and `rw` matches syntactically, so re-index the exponent
  -- with `omega` before the degree lemmas can fire.
  rw [show k - i = i + (k - 2 * i) by omega,
    deg_heckeTDiag_eq_diagCoset_degree (pow_pos hp.pos i) (pow_pos hp.pos _)
      (Nat.pow_dvd_pow p (Nat.le_add_right i _)),
    degree_diagCoset_prime_pow p hp i (k - 2 * i) (by omega)]

/-- The middle term of the `T(pᵏ)` expansion, where the two exponents agree, has degree
one. -/
private lemma deg_prime_pow_term_eq (hp : p.Prime) (i k : ℕ) (h2i : 2 * i = k) :
    deg (posDetInt 2) (SLnZ 2) ℤ (heckeTDiag (p ^ i) (p ^ (k - i))) = 1 := by
  -- Two shape mismatches `rw` cannot bridge on its own: truncated ℕ-subtraction hides `k - i = i`,
  -- and `degree_diagCoset_const` is stated for a constant *function*, which `![x, x]` is only
  -- extensionally — hence the `funext`.
  rw [show k - i = i by omega,
    deg_heckeTDiag_eq_diagCoset_degree (pow_pos hp.pos i) (pow_pos hp.pos i) dvd_rfl,
    show ![p ^ i, p ^ i] = (fun _ : Fin 2 ↦ p ^ i) from funext fun j ↦ by fin_cases j <;> rfl,
    degree_diagCoset_const 2 _, Nat.cast_one]

/-- Raising the exponent by two shifts the expansion of `T(pᵏ)` by one place without
changing any term's degree. -/
private lemma deg_prime_pow_shift (hp : p.Prime) (i k : ℕ) (hi : i < k / 2 + 1) :
    deg (posDetInt 2) (SLnZ 2) ℤ (heckeTDiag (p ^ (i + 1)) (p ^ (k + 2 - (i + 1)))) =
      deg (posDetInt 2) (SLnZ 2) ℤ (heckeTDiag (p ^ i) (p ^ (k - i))) := by
  rcases lt_or_ge (2 * i) k with h2i | h2i
  · -- Both sides are now `p ^ _ * (p + 1)` and differ only in how truncated ℕ-subtraction
    -- writes the exponent, which `omega` reconciles.
    rw [deg_prime_pow_term_lt p hp (i + 1) (k + 2) (by omega),
      deg_prime_pow_term_lt p hp i k h2i, show k + 2 - 2 * (i + 1) - 1 = k - 2 * i - 1 by omega]
  · rw [deg_prime_pow_term_eq p hp (i + 1) (k + 2) (by omega),
      deg_prime_pow_term_eq p hp i k (by omega)]

/-- The inductive step of `deg_heckeT_prime_pow`, from `k` to `k + 2`. -/
private lemma deg_heckeT_prime_pow_step (hp : p.Prime) (k : ℕ)
    (ih : deg (posDetInt 2) (SLnZ 2) ℤ (heckeT ⟨p ^ k, pow_pos hp.pos k⟩) =
      ∑ j ∈ Finset.range (k + 1), (p : ℤ) ^ j) :
    deg (posDetInt 2) (SLnZ 2) ℤ (heckeT ⟨p ^ (k + 2), pow_pos hp.pos (k + 2)⟩) =
      ∑ j ∈ Finset.range (k + 2 + 1), (p : ℤ) ^ j := by
  rw [heckeT_prime_pow_expansion p hp (k + 2), map_sum, Nat.add_div_right k two_pos,
    Finset.sum_range_succ']
  have h_tail : ∑ i ∈ Finset.range (k / 2 + 1),
      deg (posDetInt 2) (SLnZ 2) ℤ (heckeTDiag (p ^ (i + 1)) (p ^ (k + 2 - (i + 1)))) =
      ∑ i ∈ Finset.range (k / 2 + 1),
        deg (posDetInt 2) (SLnZ 2) ℤ (heckeTDiag (p ^ i) (p ^ (k - i))) :=
    Finset.sum_congr rfl fun i hi ↦ deg_prime_pow_shift p hp i k (Finset.mem_range.mp hi)
  rw [heckeT_prime_pow_expansion p hp k, map_sum] at ih
  -- `Finset.sum_range_succ'` peels off the `i = 0` term, which `deg_prime_pow_term_lt` returns
  -- with the exponent written as `k + 2 - 2 * 0 - 1`; `omega` normalises that to `k + 1`.
  rw [h_tail, ih, show deg (posDetInt 2) (SLnZ 2) ℤ (heckeTDiag (p ^ 0) (p ^ (k + 2 - 0))) =
      ((p ^ (k + 1) * (p + 1) : ℕ) : ℤ) by
    simpa [show k + 2 - 2 * 0 - 1 = k + 1 by omega] using
      deg_prime_pow_term_lt p hp 0 (k + 2) (by omega)]
  conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  ring

/-- **The prime-power degree** (Shimura, Theorem 3.24(7) at a prime power):
`deg T(pᵏ) = 1 + p + ⋯ + pᵏ`. -/
theorem deg_heckeT_prime_pow (hp : p.Prime) (k : ℕ) :
    deg (posDetInt 2) (SLnZ 2) ℤ (heckeT ⟨p ^ k, pow_pos hp.pos k⟩) =
      ∑ j ∈ Finset.range (k + 1), (p : ℤ) ^ j := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [heckeT_prime_pow_expansion p hp 1, map_sum]
    simpa using deg_prime_pow_term_lt p hp 0 1 (by omega)
  | more k ih _ => exact deg_heckeT_prime_pow_step p hp k ih

/-- **The degree of `T(m)`** (Shimura, Theorem 3.24(7)): `deg T(m) = σ₁(m)`. -/
-- `@[simp]` on the unconditional formula only: `deg_heckeT_prime_pow` is the instance
-- `m = ⟨p ^ k, _⟩` of this one, so annotating both would leave the specialized form unreachable.
@[simp]
theorem deg_heckeT (m : ℕ+) :
    deg (posDetInt 2) (SLnZ 2) ℤ (heckeT m) = (σ 1) (m : ℕ) := by
  obtain ⟨n, hn⟩ := m
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [deg_heckeT_prime_pow p hp k]
    exact_mod_cast (ArithmeticFunction.sigma_one_apply_prime_pow hp).symm
  | zero => exact absurd hn (lt_irrefl 0)
  | one => simp
  | coprime p q hp hq hcop ihp ihq =>
    have hp_pos : 0 < p := zero_lt_one.trans hp
    have hq_pos : 0 < q := zero_lt_one.trans hq
    rw [show heckeT ⟨p * q, hn⟩ = heckeT ⟨p, hp_pos⟩ * heckeT ⟨q, hq_pos⟩ from
      (heckeT_mul_of_coprime ⟨p, hp_pos⟩ ⟨q, hq_pos⟩ hcop).symm, map_mul, ihp hp_pos, ihq hq_pos]
    exact_mod_cast (ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop).symm

end HeckeRing.GL2
