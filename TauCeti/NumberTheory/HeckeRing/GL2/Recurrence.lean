/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.MultiplicationTable

import TauCeti.Algebra.LinearRecurrence.OrderTwo
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The `GL₂` multiplication table: the prime-power recurrence

Shimura's Theorem 3.24(4): the summed Hecke operators at a prime satisfy

`T(p^(k+1)) = T(p) · T(pᵏ) − p · T(p,p) · T(p^(k−1))`   for `k ≥ 1`,

which determines every `T(pᵏ)` from `T(p)` and the scalar operator. The proof feeds the
key product identity `T(p) · T(1,pᵏ) = T(1,p^(k+1)) + m · T(p,pᵏ)` into the telescoping
identity `T(1,pᵏ) = T(pᵏ) − T(p,p) · T(p^(k−2))`, by strong induction on `k`.

The recurrence then yields the full product formula
`T(pʳ) · T(pˢ) = ∑_{i ≤ r} pⁱ · T(p,p)ⁱ · T(p^(r+s−2i))` for `r ≤ s`, again by strong
induction: each summand splits in two through the recurrence, and the scalar operator is
central, so the shifted copy cancels against the subtracted term.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), recurrence section.

## Main results

* `HeckeRing.GL2.heckeTDiag_p_prime_pow_eq`: `T(p, pᵏ) = T(p,p) · T(1, p^(k−1))`.
* `HeckeRing.GL2.heckeT_prime_pow_recurrence`: the prime-power recurrence.
* `HeckeRing.GL2.heckeT_prime_pow_mul`: the product formula
  `T(pʳ) · T(pˢ) = ∑_{i ≤ r} pⁱ · T(p,p)ⁱ · T(p^(r+s−2i))` for `r ≤ s`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Theorem 3.24.
-/

public section

open Matrix HeckeRing DoubleCoset Finset HeckeRing.GLn

namespace HeckeRing.GL2

variable (p : ℕ) (hp : p.Prime)

omit hp in
/-- `T(p, pᵏ) = T(p,p) · T(1, p^(k−1))` for `k ≥ 1`: the index shift at the bottom of the
divisor pair.

Like the index shift it specializes, this is unconditional: `heckeTDiag` is zero-extended,
so no positivity or primality hypothesis is needed. -/
lemma heckeTDiag_p_prime_pow_eq (k : ℕ) (hk : 0 < k) :
    heckeTDiag p (p ^ k) = heckeTScalar p * heckeTDiag 1 (p ^ (k - 1)) := by
  have h0 := heckeTScalar_mul_heckeTDiag_prime_pow p 0 (k - 1)
  rw [show k - 1 + 1 = k from Nat.succ_pred_eq_of_pos hk] at h0
  simpa [pow_zero, zero_add, pow_one] using h0.symm

include hp in
/-- `T(p⁰) = 1`.

Not a restatement of `heckeT_one`: the work is normalizing the `ℕ+` *index* `⟨p ^ 0, _⟩` to
`1`, which needs `Subtype.ext` and so cannot be reached by rewriting `pow_zero` under the
positivity proof. Used at four call sites. -/
private lemma heckeT_prime_pow_zero : heckeT ⟨p ^ 0, pow_pos hp.pos 0⟩ = 1 := by
  rw [show (⟨p ^ 0, pow_pos hp.pos 0⟩ : ℕ+) = 1 from Subtype.ext (pow_zero p)]
  exact heckeT_one

omit hp in
/-- `T(1, p¹) = T(1, p)`.

Deliberately *not* inlined as `pow_one`. In the goals where it is used, `p ^ 1` also occurs as
`heckeT ⟨p ^ 1, _⟩`, where the exponent appears inside the positivity proof; rewriting with
`pow_one` there fails with "motive is not type correct". Stating the rewrite against
`heckeTDiag` confines it to the one occurrence that carries no dependent proof. -/
private lemma heckeTDiag_one_prime_pow_one : heckeTDiag 1 (p ^ 1) = heckeTDiag 1 p := by
  rw [pow_one]

include hp in
/-- `T(p¹) = T(p)`: normalizing the exponent in the index.

As with `heckeT_prime_pow_zero`, the content is the `ℕ+` index equality `⟨p ^ 1, _⟩ = ⟨p, _⟩`,
which `Subtype.ext` supplies and a bare `pow_one` rewrite cannot, since the exponent also
occurs inside the positivity proof. Used at four call sites. -/
private lemma heckeT_prime_pow_one : heckeT ⟨p ^ 1, pow_pos hp.pos 1⟩ = heckeT ⟨p, hp.pos⟩ := by
  congr 1
  exact Subtype.ext (pow_one p)

include hp in
/-- The inductive step of the recurrence for exponents `≥ 3`: substitute the recurrence at
`k` into the key product identity, then rearrange. -/
private lemma heckeT_prime_pow_recurrence_step (k : ℕ) (hk_pos : 0 < k)
    (ih : ∀ j : ℕ, j < k + 2 → 0 < j →
      heckeT ⟨p ^ (j + 1), pow_pos hp.pos (j + 1)⟩ =
        heckeT ⟨p, hp.pos⟩ * heckeT ⟨p ^ j, pow_pos hp.pos j⟩ -
          (p : ℤ) • (heckeTScalar p * heckeT ⟨p ^ (j - 1), pow_pos hp.pos (j - 1)⟩)) :
    heckeT ⟨p ^ (k + 2 + 1), pow_pos hp.pos (k + 2 + 1)⟩ =
      heckeT ⟨p, hp.pos⟩ * heckeT ⟨p ^ (k + 2), pow_pos hp.pos (k + 2)⟩ -
        (p : ℤ) • (heckeTScalar p * heckeT ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩) := by
  have h5 := heckeT_prime_mul_heckeTDiag_one_prime_pow p hp (k + 2)
  rw [heckeTDiag_p_prime_pow_eq p (k + 2) (by omega)] at h5
  have h2 := heckeTDiag_one_prime_pow_eq p hp (k + 2 + 1) (by omega)
  conv at h2 => rhs; rw [show (k + 2 + 1) - 2 = k + 1 by omega]
  rw [h2] at h5
  simp only [show k + 2 ≠ 1 by omega, ite_false, show k + 2 - 1 = k + 1 by omega] at h5
  rw [heckeTDiag_one_prime_pow_eq p hp (k + 2) (by omega)] at h5
  -- distribute `T(p)` over the telescoped difference
  rw [mul_sub] at h5
  have h2k1 := heckeTDiag_one_prime_pow_eq p hp (k + 1) (by omega)
  conv at h2k1 => rhs; rw [show (k + 1) - 2 = k - 1 by omega]
  rw [h2k1] at h5
  conv at h5 => lhs; rw [show k + 2 - 2 = k by omega]
  -- and `T(p,p)` over the difference on the right
  conv at h5 => rhs; rw [mul_sub]
  -- the scalar operator is central, and the induction hypothesis rewrites `T(p) · T(pᵏ)`
  have hcomm : heckeT ⟨p, hp.pos⟩ * heckeTScalar p =
      heckeTScalar p * heckeT ⟨p, hp.pos⟩ := by
    rw [heckeT_prime p hp]
    exact HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution 2)
      (transposeAntiInvolution_onHeckeCoset_eq_self 2) (heckeTDiag 1 p) (heckeTScalar p)
  have hih : heckeT ⟨p, hp.pos⟩ * heckeT ⟨p ^ k, pow_pos hp.pos k⟩ =
      heckeT ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ +
        (p : ℤ) • (heckeTScalar p * heckeT ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) := by
    rw [ih k (by omega) hk_pos]
    abel
  rw [smul_sub,
    ← mul_assoc (heckeT ⟨p, hp.pos⟩) (heckeTScalar p)
      (heckeT ⟨p ^ k, pow_pos hp.pos k⟩),
    hcomm,
    mul_assoc (heckeTScalar p) (heckeT ⟨p, hp.pos⟩)
      (heckeT ⟨p ^ k, pow_pos hp.pos k⟩),
    hih, mul_add (heckeTScalar p), mul_smul_comm (p : ℤ),
    ← mul_assoc (heckeTScalar p) (heckeTScalar p), sub_eq_iff_eq_add] at h5
  linear_combination (norm := module) -h5

include hp in
/-- **Shimura, Theorem 3.24(4)** — the prime-power recurrence:
`T(p^(k+1)) = T(p) · T(pᵏ) − p · T(p,p) · T(p^(k−1))` for `k ≥ 1`, which determines every
`T(pᵏ)` from `T(p)` and the scalar operator. -/
theorem heckeT_prime_pow_recurrence : ∀ k : ℕ, 0 < k →
    heckeT ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ =
      heckeT ⟨p, hp.pos⟩ * heckeT ⟨p ^ k, pow_pos hp.pos k⟩ -
        (p : ℤ) • (heckeTScalar p * heckeT ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro hk
  have h5 := heckeT_prime_mul_heckeTDiag_one_prime_pow p hp k
  rw [heckeTDiag_p_prime_pow_eq p k hk] at h5
  have h2 := heckeTDiag_one_prime_pow_eq p hp (k + 1) (by omega)
  conv at h2 => rhs; rw [show (k + 1) - 2 = k - 1 by omega]
  rw [h2] at h5
  rcases k with _ | k
  · omega
  rcases k with _ | k
  · simp only [show (1 : ℕ) - 1 = 0 from rfl, ite_true] at h5 ⊢
    rw [heckeT_prime_pow_zero p hp, pow_zero, heckeTDiag_one_one, mul_one] at h5
    rw [heckeT_prime_pow_zero p hp, mul_one, heckeT_prime_pow_one p hp]
    rw [heckeTDiag_one_prime_pow_one, heckeT_prime p hp] at h5
    rw [heckeT_prime p hp]
    -- split the `k = 1` coefficient `p + 1` into `p` and the unit
    rw [add_smul, one_smul] at h5
    linear_combination (norm := module) -h5
  rcases k with _ | k
  · simp only [show (2 : ℕ) ≠ 1 by omega, ite_false, show (2 : ℕ) - 1 = 1 by omega] at h5 ⊢
    rw [heckeTDiag_one_prime_pow_eq p hp 2 (by omega)] at h5
    rw [mul_sub] at h5
    simp only [show 2 - 2 = 0 from rfl] at h5 ⊢
    rw [heckeT_prime_pow_zero p hp, mul_one, heckeTDiag_one_prime_pow_one, heckeT_prime p hp] at h5
    rw [heckeT_prime_pow_one p hp] at h5 ⊢
    rw [heckeT_prime p hp] at h5 ⊢
    rw [HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution 2)
      (transposeAntiInvolution_onHeckeCoset_eq_self 2) (heckeTDiag 1 p) (heckeTScalar p)] at h5
    linear_combination (norm := module) -h5
  · exact heckeT_prime_pow_recurrence_step p hp (k + 1) (by omega) ih

section Centrality

/-! ## The product formula

`r ↦ T(pʳ)` is a second-order linear recurrence: `heckeT_prime_pow_recurrence` says it obeys
`d (r + 2) = D * d (r + 1) - S * d r` with `D = T(p)` and `S = p • T(p,p)`. The product formula
is therefore an instance of `TauCeti.linearRec₂_mul_eq_sum_pow_mul`, which holds for any such
sequence over any ring in which `D` and `S` commute — and here they do, the scalar operator
being central. -/

include hp in
/-- `T(p)` commutes with the scalar operator `p • T(p,p)`.

The scalar operator is central by `mul_comm_of_antiInvolution`, and an integer multiple of a
commuting element still commutes. -/
private lemma commute_heckeT_prime_smul_heckeTScalar :
    Commute (heckeT ⟨p, hp.pos⟩) ((p : ℤ) • heckeTScalar p) := by
  refine Commute.smul_right ?_ _
  rw [heckeT_prime p hp]
  exact HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution 2)
    (transposeAntiInvolution_onHeckeCoset_eq_self 2) (heckeTDiag 1 p) (heckeTScalar p)

include hp in
/-- **Shimura, Theorem 3.24(4)** — the prime-power product formula:
`T(pʳ) · T(pˢ) = ∑_{i ≤ r} pⁱ · T(p,p)ⁱ · T(p^(r+s−2i))` for `r ≤ s`.

This is `TauCeti.linearRec₂_mul_eq_sum_pow_mul` at `d = fun r ↦ T(pʳ)`, `D = T(p)` and
`S = p • T(p,p)`; all that is left is to match the summand, since the general statement writes
`S ^ i * _` where this one writes `pⁱ • (T(p,p)ⁱ * _)`. -/
theorem heckeT_prime_pow_mul : ∀ r s : ℕ, r ≤ s →
    heckeT ⟨p ^ r, pow_pos hp.pos r⟩ * heckeT ⟨p ^ s, pow_pos hp.pos s⟩ =
      ∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ i • (heckeTScalar p ^ i *
        heckeT ⟨p ^ (r + s - 2 * i), pow_pos hp.pos (r + s - 2 * i)⟩) := by
  intro r s hrs
  have hrec : ∀ n : ℕ, heckeT ⟨p ^ (n + 2), pow_pos hp.pos (n + 2)⟩ =
      heckeT ⟨p, hp.pos⟩ * heckeT ⟨p ^ (n + 1), pow_pos hp.pos (n + 1)⟩ -
        ((p : ℤ) • heckeTScalar p) * heckeT ⟨p ^ n, pow_pos hp.pos n⟩ := by
    intro n
    have h := heckeT_prime_pow_recurrence p hp (n + 1) (by omega)
    rw [show n + 1 + 1 = n + 2 by omega, show n + 1 - 1 = n by omega] at h
    rw [h, smul_mul_assoc]
  rw [TauCeti.linearRec₂_mul_eq_sum_pow_mul (d := fun n ↦ heckeT ⟨p ^ n, pow_pos hp.pos n⟩)
    (heckeT_prime_pow_zero p hp) (heckeT_prime_pow_one p hp)
    (commute_heckeT_prime_smul_heckeTScalar p hp) hrec hrs]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_pow, smul_mul_assoc]


end Centrality

end HeckeRing.GL2
