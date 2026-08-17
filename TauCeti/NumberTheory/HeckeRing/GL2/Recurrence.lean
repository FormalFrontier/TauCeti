/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.MultiplicationTable

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

/-! ## Centrality of the scalar operator

The scalar operator commutes with every summed operator, hence so do its powers. -/

include hp in
/-- Powers of the scalar operator commute with `T(pᵏ)`.

The scalar operator is central by `mul_comm_of_antiInvolution`; that a commuting element's
powers still commute is `Commute.pow_left`, so there is nothing to induct on here. -/
private lemma commute_heckeTScalar_pow_heckeT_prime_pow (i k : ℕ) :
    Commute (heckeTScalar p ^ i) (heckeT ⟨p ^ k, pow_pos hp.pos k⟩) :=
  Commute.pow_left (HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution 2)
    (transposeAntiInvolution_onHeckeCoset_eq_self 2) (heckeTScalar p)
      (heckeT ⟨p ^ k, pow_pos hp.pos k⟩)) i

include hp in
/-- `T(p)` passes through a scalar power in front of any `T(pᵏ)`. -/
private lemma heckeT_prime_mul_scalar_pow_mul (i k : ℕ) :
    heckeT ⟨p, hp.pos⟩ * (heckeTScalar p ^ i * heckeT ⟨p ^ k, pow_pos hp.pos k⟩) =
      heckeTScalar p ^ i * (heckeT ⟨p, hp.pos⟩ * heckeT ⟨p ^ k, pow_pos hp.pos k⟩) := by
  rw [← mul_assoc, ← heckeT_prime_pow_one p hp,
    (commute_heckeTScalar_pow_heckeT_prime_pow p hp i 1).symm.eq, mul_assoc]

include hp in
/-- Each summand of `T(p) · S` splits in two through the recurrence. -/
private lemma heckeT_prime_pow_mul_summand_split (r s i : ℕ) (hi : i ≤ r) (hrs : r ≤ s) :
    (p : ℤ) ^ i • (heckeTScalar p ^ i *
        (heckeT ⟨p, hp.pos⟩ *
          heckeT ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos (r + 1 + s - 2 * i)⟩)) =
      (p : ℤ) ^ i • (heckeTScalar p ^ i *
          heckeT ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos (r + 2 + s - 2 * i)⟩) +
        (p : ℤ) ^ (i + 1) • (heckeTScalar p ^ (i + 1) *
          heckeT ⟨p ^ (r + s - 2 * i), pow_pos hp.pos (r + s - 2 * i)⟩) := by
  have h_rec := heckeT_prime_pow_recurrence p hp (r + 1 + s - 2 * i) (by omega)
  rw [show r + 1 + s - 2 * i + 1 = r + 2 + s - 2 * i by omega,
    show r + 1 + s - 2 * i - 1 = r + s - 2 * i by omega] at h_rec
  have h_eq : heckeT ⟨p, hp.pos⟩ *
      heckeT ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos (r + 1 + s - 2 * i)⟩ =
      heckeT ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos (r + 2 + s - 2 * i)⟩ +
        (p : ℤ) • (heckeTScalar p *
          heckeT ⟨p ^ (r + s - 2 * i), pow_pos hp.pos (r + s - 2 * i)⟩) := by
    rw [eq_sub_iff_add_eq] at h_rec
    exact h_rec.symm
  rw [h_eq, mul_add, smul_add]
  congr 1
  rw [mul_smul_comm, smul_smul, show (p : ℤ) ^ i * (p : ℤ) = (p : ℤ) ^ (i + 1) by ring]
  congr 1
  rw [← mul_assoc, ← pow_succ]

include hp in
/-- Distribute `T(p)` into each summand of a product-formula sum. -/
private lemma heckeT_prime_mul_sum_distrib (r s : ℕ) :
    heckeT ⟨p, hp.pos⟩ *
      (∑ i ∈ Finset.range (r + 1 + 1), (p : ℤ) ^ i • (heckeTScalar p ^ i *
        heckeT ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos (r + 1 + s - 2 * i)⟩)) =
      ∑ i ∈ Finset.range (r + 1 + 1), (p : ℤ) ^ i • (heckeTScalar p ^ i *
        (heckeT ⟨p, hp.pos⟩ *
          heckeT ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos (r + 1 + s - 2 * i)⟩)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_smul_comm, heckeT_prime_mul_scalar_pow_mul p hp i _, ← mul_assoc]

include hp in
/-- Distribute `p · T(p,p)` into a product-formula sum, shifting the index. -/
private lemma heckeT_scalar_mul_sum_shift (r s : ℕ) :
    (p : ℤ) • (heckeTScalar p *
      ∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ i • (heckeTScalar p ^ i *
        heckeT ⟨p ^ (r + s - 2 * i), pow_pos hp.pos (r + s - 2 * i)⟩)) =
      ∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ (i + 1) • (heckeTScalar p ^ (i + 1) *
        heckeT ⟨p ^ (r + s - 2 * i), pow_pos hp.pos (r + s - 2 * i)⟩) := by
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_smul_comm, smul_smul, mul_comm ((p : ℤ)) ((p : ℤ) ^ i), ← pow_succ]
  congr 1
  rw [← mul_assoc, ← pow_succ']

include hp in
/-- The top-index summand expands through the recurrence at `p^(s−r−1)`. -/
private lemma heckeT_prime_pow_mul_summand_split_succ (r s : ℕ) (hrs : r + 2 ≤ s) :
    (p : ℤ) ^ (r + 1) • (heckeTScalar p ^ (r + 1) *
        (heckeT ⟨p, hp.pos⟩ *
          heckeT ⟨p ^ (r + 1 + s - 2 * (r + 1)),
            pow_pos hp.pos (r + 1 + s - 2 * (r + 1))⟩)) =
      (p : ℤ) ^ (r + 1) • (heckeTScalar p ^ (r + 1) *
          heckeT ⟨p ^ (r + 2 + s - 2 * (r + 1)),
            pow_pos hp.pos (r + 2 + s - 2 * (r + 1))⟩) +
        (p : ℤ) ^ (r + 2) • (heckeTScalar p ^ (r + 2) *
          heckeT ⟨p ^ (r + 2 + s - 2 * (r + 2)),
            pow_pos hp.pos (r + 2 + s - 2 * (r + 2))⟩) := by
  have hexp : r + 1 + s - 2 * (r + 1) = s - r - 1 := by omega
  have h_rec := heckeT_prime_pow_recurrence p hp (s - r - 1) (by omega)
  rw [show s - r - 1 + 1 = s - r by omega, show s - r - 1 - 1 = s - r - 2 by omega] at h_rec
  have h_expand : heckeT ⟨p, hp.pos⟩ * heckeT ⟨p ^ (s - r - 1), pow_pos hp.pos (s - r - 1)⟩ =
      heckeT ⟨p ^ (s - r), pow_pos hp.pos (s - r)⟩ +
        (p : ℤ) • (heckeTScalar p * heckeT ⟨p ^ (s - r - 2), pow_pos hp.pos (s - r - 2)⟩) := by
    rw [eq_sub_iff_add_eq] at h_rec
    exact h_rec.symm
  rw [hexp, h_expand, mul_add, smul_add, mul_smul_comm, smul_smul,
    show (p : ℤ) ^ (r + 1) * (p : ℤ) = (p : ℤ) ^ (r + 2) by ring, ← mul_assoc,
    show heckeTScalar p ^ (r + 1) * heckeTScalar p = heckeTScalar p ^ (r + 2) from
      (pow_succ (heckeTScalar p) (r + 1)).symm]
  rw [show s - r - 2 = r + 2 + s - 2 * (r + 2) by omega,
    show s - r = r + 2 + s - 2 * (r + 1) by omega]

include hp in
/-- The inductive step of the product formula: from the formula at `r` and `r + 1` against
`s`, it follows at `r + 2`. -/
private lemma heckeT_prime_pow_mul_step (r s : ℕ) (hrs : r + 2 ≤ s)
    (ih1 : heckeT ⟨p ^ (r + 1), pow_pos hp.pos (r + 1)⟩ * heckeT ⟨p ^ s, pow_pos hp.pos s⟩ =
      ∑ i ∈ Finset.range (r + 1 + 1), (p : ℤ) ^ i • (heckeTScalar p ^ i *
        heckeT ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos (r + 1 + s - 2 * i)⟩))
    (ih0 : heckeT ⟨p ^ r, pow_pos hp.pos r⟩ * heckeT ⟨p ^ s, pow_pos hp.pos s⟩ =
      ∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ i • (heckeTScalar p ^ i *
        heckeT ⟨p ^ (r + s - 2 * i), pow_pos hp.pos (r + s - 2 * i)⟩)) :
    heckeT ⟨p ^ (r + 2), pow_pos hp.pos (r + 2)⟩ * heckeT ⟨p ^ s, pow_pos hp.pos s⟩ =
      ∑ i ∈ Finset.range (r + 2 + 1), (p : ℤ) ^ i • (heckeTScalar p ^ i *
        heckeT ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos (r + 2 + s - 2 * i)⟩) := by
  have h_rec := heckeT_prime_pow_recurrence p hp (r + 1) (by omega)
  simp only [show r + 1 - 1 = r by omega] at h_rec
  rw [show r + 1 + 1 = r + 2 by omega] at h_rec
  rw [h_rec, sub_mul, mul_assoc, ih1, smul_mul_assoc, mul_assoc (heckeTScalar p), ih0]
  set Tp := heckeT ⟨p, hp.pos⟩
  set Tpp := heckeTScalar p
  have h_lhs1 := heckeT_prime_mul_sum_distrib p hp r s
  have h_lhs2 := heckeT_scalar_mul_sum_shift p hp r s
  have h_sum_split : ∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ i • (Tpp ^ i *
        (Tp * heckeT ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos (r + 1 + s - 2 * i)⟩)) =
      (∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ i • (Tpp ^ i *
          heckeT ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos (r + 2 + s - 2 * i)⟩)) +
        (∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ (i + 1) • (Tpp ^ (i + 1) *
          heckeT ⟨p ^ (r + s - 2 * i), pow_pos hp.pos (r + s - 2 * i)⟩)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    exact heckeT_prime_pow_mul_summand_split p hp r s i (by omega) (by omega)
  rw [h_lhs1, Finset.sum_range_succ, h_sum_split, h_lhs2]
  set A := ∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ i • (Tpp ^ i *
    heckeT ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos (r + 2 + s - 2 * i)⟩)
  set B := ∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ (i + 1) • (Tpp ^ (i + 1) *
    heckeT ⟨p ^ (r + s - 2 * i), pow_pos hp.pos (r + s - 2 * i)⟩)
  set C := (p : ℤ) ^ (r + 1) • (Tpp ^ (r + 1) *
    (Tp * heckeT ⟨p ^ (r + 1 + s - 2 * (r + 1)), pow_pos hp.pos (r + 1 + s - 2 * (r + 1))⟩))
  -- `A`, `B`, `C` are `set` abbreviations, so the goal is already this sum up to defeq;
  -- no rewrite witnesses that regrouping, hence `change` rather than `rw`
  change A + B + C - B = _
  rw [add_assoc, add_comm B C, ← add_assoc, add_sub_cancel_right,
    show r + 2 + 1 = r + 1 + 1 + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
  congr 1
  exact heckeT_prime_pow_mul_summand_split_succ p hp r s hrs

include hp in
/-- **Shimura, Theorem 3.24(4)** — the prime-power product formula:
`T(pʳ) · T(pˢ) = ∑_{i ≤ r} pⁱ · T(p,p)ⁱ · T(p^(r+s−2i))` for `r ≤ s`. -/
theorem heckeT_prime_pow_mul : ∀ r s : ℕ, r ≤ s →
    heckeT ⟨p ^ r, pow_pos hp.pos r⟩ * heckeT ⟨p ^ s, pow_pos hp.pos s⟩ =
      ∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ i • (heckeTScalar p ^ i *
        heckeT ⟨p ^ (r + s - 2 * i), pow_pos hp.pos (r + s - 2 * i)⟩) := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro s hrs
  rcases r with _ | _ | r
  · rw [Finset.sum_range_one, heckeT_prime_pow_zero p hp]
    simp
  · rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pow_zero, one_smul, one_mul, pow_one]
    conv_rhs => rw [show 0 + 1 + s - 2 * 0 = s + 1 by omega,
      show 0 + 1 + s - 2 * 1 = s - 1 by omega]
    rw [heckeT_prime_pow_one p hp]
    exact (eq_sub_iff_add_eq.mp (heckeT_prime_pow_recurrence p hp s (by omega))).symm
  · exact heckeT_prime_pow_mul_step p hp r s (by omega) (ih (r + 1) (by omega) s (by omega))
      (ih r (by omega) s (by omega))

end Centrality

end HeckeRing.GL2
