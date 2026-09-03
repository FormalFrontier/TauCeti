/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Associative
public import Mathlib.RingTheory.Binomial
public import TauCeti.Algebra.Module.Rat
import TauCeti.RingTheory.Binomial
import TauCeti.RingTheory.DividedPowers.Commutation
import Mathlib.Tactic.NoncommRing

/-!
# Rank-one Kostant straightening

This file proves the rank-one straightening formula for divided powers in an associative
`ℚ`-algebra. If `H`, `E`, and `F` satisfy the `sl₂` commutator relations, then

```text
E * F - F * E = H,   H * E - E * H = 2 • E,   H * F - F * H = -(2 • F),

E⁽ᵐ⁾ F⁽ⁿ⁾ =
  ∑ k ≤ min(m,n), F⁽ⁿ⁻ᵏ⁾ (H - m - n + 2k choose k) E⁽ᵐ⁻ᵏ⁾.
```

All coefficients are generalized binomial coefficients, so the formula is integral even though
the individual divided powers are defined using rational factorial denominators. This is the
rank-one normal-ordering relation needed for the integral PBW theorem for a Kostant form.

The proof follows the usual induction on `m`. Moving one additional `E` through the lowering
divided power produces two adjacent summands. `TauCeti.Ring.mul_weighted_choose_add_mul_choose`
combines their Cartan coefficients without division.

## Main results

* `TauCeti.Sl2.dividedPower_e_mul_dividedPower_f`: the rank-one Kostant straightening formula in an
  arbitrary associative `ℚ`-algebra satisfying the three displayed commutator relations.
* `TauCeti.Sl2.dividedPower_ι_e_mul_dividedPower_ι_f`: its specialization to the canonical map
  into a universal enveloping algebra, stated from the corresponding Lie-bracket relations.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Sl2

open Finset
open Associative

universe u

attribute [local instance] TauCeti.moduleNNRat

variable {A : Type u} [Ring A] [Algebra ℚ A]

private noncomputable def straighteningSummand (H E F : A) (m n k : ℕ) : A :=
  dividedPower (n - k) F *
    Ring.choose (H - (m + n : ℕ) + (2 * k : ℕ)) k *
      dividedPower (m - k) E

private theorem straighteningSummand_zero_left (H E F : A) (n : ℕ) :
    straighteningSummand H E F 0 n 0 = dividedPower n F := by
  simp [straighteningSummand]

private theorem weighted_straightening_coefficient (r : A) (m j : ℕ) (hj : j ≤ m + 1)
    (hj0 : 0 < j) :
    (m + 1 - j) • Ring.choose (r - 1) j +
        (r + (m + 1 - j : ℕ)) * Ring.choose (r - 1) (j - 1) =
      (m + 1) • Ring.choose r j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj0)
  have hk : k ≤ m := by omega
  have h := TauCeti.Ring.mul_weighted_choose_add_mul_choose
    r (m - k : ℕ) (R := A) k
  have hc : m + 1 - (k + 1) = m - k := by omega
  rw [hc]
  rw [Nat.succ_sub_one]
  simp only [nsmul_eq_mul'] at h ⊢
  have hcast : ((m + 1 : ℕ) : A) = (m - k : ℕ) + (k + 1 : ℕ) := by
    rw [← Nat.cast_add]
    congr 1
    omega
  rw [← (Nat.cast_commute (m - k) (Ring.choose (r - 1) (k + 1))).eq,
    hcast, mul_add, ← (Nat.cast_commute (m - k) (Ring.choose r (k + 1))).eq]
  exact h

private theorem e_mul_ringChoose_of_commutator {E a : A}
    (ha : a * E = E * (a + 2)) (k : ℕ) :
    E * Ring.choose a k = Ring.choose (a - 2) k * E := by
  have h := Associative.dividedPower_mul_ringChoose k ha (Nat.cast_commute 2 E) 1
  simpa using h

omit [Algebra ℚ A] in
private theorem shifted_cartan_mul_e {H E : A} (hhe : H * E - E * H = 2 • E)
    (a b : ℕ) :
    (H - (a : A) + (b : A)) * E = E * (H - (a : A) + (b : A) + 2) := by
  have hH : H * E = E * H + 2 • E := by
    simpa only [add_comm] using eq_add_of_sub_eq hhe
  simp only [sub_mul, add_mul, mul_add, hH]
  rw [(Nat.cast_commute a E).eq, (Nat.cast_commute b E).eq]
  have htwo : E * (2 : A) = 2 • E := by simpa using (nsmul_eq_mul' E 2).symm
  rw [htwo]
  simp only [mul_sub]
  abel

private noncomputable def raisedStraighteningSummand (H E F : A) (m n k : ℕ) : A :=
  dividedPower (n - (k + 1)) F *
    ((H - (m + 1 + n : ℕ) + (2 * (k + 1) : ℕ)) + (m - k : ℕ)) *
      Ring.choose (H - (m + n : ℕ) + (2 * k : ℕ)) k *
        dividedPower (m - k) E

private noncomputable def keptStraighteningSummand (H E F : A) (m n k : ℕ) : A :=
  (m + 1 - k) •
    (dividedPower (n - k) F *
      Ring.choose (H - (m + 1 + n : ℕ) + (2 * k : ℕ) - 1) k *
        dividedPower (m + 1 - k) E)

private theorem e_mul_straighteningSummand_of_lt {H E F : A}
    (hef : E * F - F * E = H) (hhe : H * E - E * H = 2 • E)
    (hhf : H * F - F * H = -(2 • F)) {m n k : ℕ} (hk : k ≤ m) (hkn : k < n) :
    E * straighteningSummand H E F m n k =
      keptStraighteningSummand H E F m n k +
        raisedStraighteningSummand H E F m n k := by
  have hnk : n - k = (n - k - 1) + 1 := by omega
  have harg :
      H - (m + n : ℕ) + (2 * k : ℕ) - 2 =
        H - (m + 1 + n : ℕ) + (2 * k : ℕ) - 1 := by
    have hmn : ((m + 1 + n : ℕ) : A) = (m + n : ℕ) + 1 := by
      push_cast
      abel
    have htwo : (2 : A) = 1 + 1 := by norm_num
    rw [hmn, htwo]
    abel
  have hnkCast : ((n - k - 1 : ℕ) : A) = (n : A) - (k : A) - 1 := by
    have hsub : n - k - 1 = n - (k + 1) := by omega
    rw [hsub, Nat.cast_sub (by omega : k + 1 ≤ n)]
    push_cast
    abel
  have hmkCast : ((m - k : ℕ) : A) = (m : A) - (k : A) := by
    rw [Nat.cast_sub hk]
  have hfactor :
      H - ((n - k - 1 : ℕ) : A) =
        (H - (m + 1 + n : ℕ) + (2 * (k + 1) : ℕ)) + (m - k : ℕ) := by
    rw [hnkCast, hmkCast]
    have hmn : ((m + 1 + n : ℕ) : A) = (m : A) + 1 + n := by push_cast; rfl
    have hk2 : ((2 * (k + 1) : ℕ) : A) = (k : A) + k + 2 := by
      have hdouble : 2 * (k + 1) = k + k + 2 := by omega
      rw [hdouble]
      push_cast
      rfl
    have htwo : (2 : A) = 1 + 1 := by norm_num
    rw [hmn, hk2, htwo]
    abel
  have hm : m + 1 - k = m - k + 1 := by omega
  have hmove := e_mul_ringChoose_of_commutator
    (shifted_cartan_mul_e hhe (m + n) (2 * k)) k
  have hfirst :
      E * (Ring.choose (H - (m + n : ℕ) + (2 * k : ℕ)) k *
          dividedPower (m - k) E) =
        (m - k + 1) •
          (Ring.choose (H - (m + 1 + n : ℕ) + (2 * k : ℕ) - 1) k *
            dividedPower (m + 1 - k) E) := by
    rw [← mul_assoc, hmove, harg, mul_assoc, self_mul_dividedPower, hm]
    simp only [nsmul_eq_mul']
    rw [mul_assoc]
  rw [straighteningSummand, mul_assoc, ← mul_assoc E]
  rw [hnk, e_mul_dividedPower_succ_f hef hhf]
  rw [add_mul]
  rw [mul_assoc (dividedPower (n - k - 1 + 1) F), hfirst]
  simp only [nsmul_eq_mul']
  rw [mul_assoc]
  simp only [keptStraighteningSummand, raisedStraighteningSummand]
  rw [hfactor]
  have hsub : n - (k + 1) = n - k - 1 := by omega
  rw [hnk, hsub]
  simp only [nsmul_eq_mul']
  rw [hm]
  noncomm_ring

private theorem e_mul_straighteningSummand_of_eq {H E F : A}
    (hhe : H * E - E * H = 2 • E) {m n k : ℕ} (hk : k ≤ m) (hkn : k = n) :
    E * straighteningSummand H E F m n k =
      keptStraighteningSummand H E F m n k := by
  subst n
  have harg :
      H - (m + k : ℕ) + (2 * k : ℕ) - 2 =
        H - (m + 1 + k : ℕ) + (2 * k : ℕ) - 1 := by
    have hmk : ((m + 1 + k : ℕ) : A) = (m + k : ℕ) + 1 := by
      push_cast
      abel
    have htwo : (2 : A) = 1 + 1 := by norm_num
    rw [hmk, htwo]
    abel
  simp only [straighteningSummand, Nat.sub_self, dividedPower_zero, one_mul]
  have hmove := e_mul_ringChoose_of_commutator
    (shifted_cartan_mul_e hhe (m + k) (2 * k)) k
  rw [← mul_assoc, hmove, harg, mul_assoc, self_mul_dividedPower]
  have hm : m + 1 - k = m - k + 1 := by omega
  simp only [keptStraighteningSummand, Nat.sub_self, dividedPower_zero, one_mul]
  rw [hm]
  simp only [nsmul_eq_mul']
  rw [mul_assoc]

private theorem keptStraighteningSummand_zero (H E F : A) (m n : ℕ) :
    keptStraighteningSummand H E F m n 0 =
      (m + 1) • straighteningSummand H E F (m + 1) n 0 := by
  simp [keptStraighteningSummand, straighteningSummand]

private theorem kept_add_raised_pred {H E F : A} (m n j : ℕ) (hj0 : 0 < j)
    (hjm : j ≤ m + 1) :
    keptStraighteningSummand H E F m n j +
        raisedStraighteningSummand H E F m n (j - 1) =
      (m + 1) • straighteningSummand H E F (m + 1) n j := by
  let r : A := H - (m + 1 + n : ℕ) + (2 * j : ℕ)
  have hcoef := weighted_straightening_coefficient r m j hjm hj0
  have hm : m - (j - 1) = m + 1 - j := by omega
  have hj : (j - 1) + 1 = j := by omega
  have harg :
      H - (m + n : ℕ) + (2 * (j - 1) : ℕ) = r - 1 := by
    dsimp [r]
    have hmn : ((m + 1 + n : ℕ) : A) = (m + n : ℕ) + 1 := by
      push_cast
      abel
    have htwoj : ((2 * j : ℕ) : A) = (2 * (j - 1) : ℕ) + 2 := by
      have hdouble : 2 * j = 2 * (j - 1) + 2 := by omega
      rw [hdouble]
      push_cast
      rfl
    have htwo : (2 : A) = 1 + 1 := by norm_num
    rw [hmn, htwoj, htwo]
    abel
  have htargetArg : H - (m + 1 + n : ℕ) + (2 * j : ℕ) = r := by rfl
  simp only [keptStraighteningSummand, raisedStraighteningSummand,
    straighteningSummand, hj, hm, harg, htargetArg]
  let X := dividedPower (n - j) F
  let Y := dividedPower (m + 1 - j) E
  let c₀ := Ring.choose (r - 1) j
  let c₁ := Ring.choose (r - 1) (j - 1)
  let c := Ring.choose r j
  -- Refold the expanded summands and coefficient identity into the abbreviations above so the
  -- final noncommutative calculation displays only the algebraic structure of the argument.
  change (m + 1 - j) • (X * c₀ * Y) + X * (r + (m + 1 - j : ℕ)) * c₁ * Y =
    (m + 1) • (X * c * Y)
  change (m + 1 - j) • c₀ + (r + (m + 1 - j : ℕ)) * c₁ = (m + 1) • c at hcoef
  simp only [nsmul_eq_mul'] at hcoef ⊢
  have hY₀ := (Nat.cast_commute (m + 1 - j) Y).eq
  have hY₁ := (Nat.cast_commute (m + 1) Y).eq
  calc
    X * c₀ * Y * ((m + 1 - j : ℕ) : A) +
        X * (r + ((m + 1 - j : ℕ) : A)) * c₁ * Y =
      X * (c₀ * ((m + 1 - j : ℕ) : A) +
        (r + ((m + 1 - j : ℕ) : A)) * c₁) * Y := by
      noncomm_ring [hY₀]
    _ = X * (c * ((m + 1 : ℕ) : A)) * Y := by rw [hcoef]
    _ = X * c * Y * ((m + 1 : ℕ) : A) := by noncomm_ring [hY₁]

private theorem sum_range_adjacent_with_zero {B : Type*} [AddCommMonoid B]
    (K R T : ℕ → B) (r : ℕ) (h₀ : T 0 = K 0)
    (hstep : ∀ j, 0 < j → j ≤ r + 1 → T j = K j + R (j - 1))
    (hbound : K (r + 1) = 0) :
    ∑ j ∈ range (r + 2), T j = ∑ k ∈ range (r + 1), (K k + R k) := by
  have hr : r + 2 = (r + 1) + 1 := by omega
  rw [hr, sum_range_succ']
  rw [h₀]
  have hsum : ∑ k ∈ range (r + 1), T (k + 1) =
      ∑ k ∈ range (r + 1), (K (k + 1) + R k) := by
    apply sum_congr rfl
    intro k hk
    rw [hstep (k + 1) (by omega) (by simpa using Nat.le_of_lt_succ (mem_range.mp hk))]
    simp
  rw [hsum, sum_add_distrib, sum_add_distrib]
  have hK : (∑ k ∈ range (r + 1), K (k + 1)) + K 0 =
      ∑ k ∈ range (r + 1), K k := by
    calc
      (∑ k ∈ range (r + 1), K (k + 1)) + K 0 =
          ∑ k ∈ range (r + 2), K k := (sum_range_succ' K (r + 1)).symm
      _ = (∑ k ∈ range (r + 1), K k) + K (r + 1) := sum_range_succ K (r + 1)
      _ = ∑ k ∈ range (r + 1), K k := by rw [hbound, add_zero]
  calc
    ((∑ k ∈ range (r + 1), K (k + 1)) + ∑ k ∈ range (r + 1), R k) + K 0 =
        ((∑ k ∈ range (r + 1), K (k + 1)) + K 0) +
          ∑ k ∈ range (r + 1), R k := by ac_rfl
    _ = (∑ k ∈ range (r + 1), K k) + ∑ k ∈ range (r + 1), R k := by rw [hK]

private theorem sum_range_adjacent_capped {B : Type*} [AddCommMonoid B]
    (K R T : ℕ → B) (r : ℕ) (h₀ : T 0 = K 0)
    (hstep : ∀ j, 0 < j → j ≤ r → T j = K j + R (j - 1)) :
    ∑ j ∈ range (r + 1), T j = (∑ k ∈ range r, (K k + R k)) + K r := by
  rw [sum_range_succ', h₀]
  have hsum : ∑ k ∈ range r, T (k + 1) =
      ∑ k ∈ range r, (K (k + 1) + R k) := by
    apply sum_congr rfl
    intro k hk
    rw [hstep (k + 1) (by omega) (Nat.succ_le_of_lt (mem_range.mp hk))]
    simp
  rw [hsum, sum_add_distrib, sum_add_distrib]
  have hshift : (∑ k ∈ range r, K (k + 1)) + K 0 =
      (∑ k ∈ range r, K k) + K r := by
    calc
      (∑ k ∈ range r, K (k + 1)) + K 0 =
          ∑ k ∈ range (r + 1), K k := (sum_range_succ' K r).symm
      _ = (∑ k ∈ range r, K k) + K r := sum_range_succ K r
  calc
    ((∑ k ∈ range r, K (k + 1)) + ∑ k ∈ range r, R k) + K 0 =
        ((∑ k ∈ range r, K (k + 1)) + K 0) + ∑ k ∈ range r, R k := by ac_rfl
    _ = ((∑ k ∈ range r, K k) + K r) + ∑ k ∈ range r, R k := by rw [hshift]
    _ = ((∑ k ∈ range r, K k) + ∑ k ∈ range r, R k) + K r := by ac_rfl

private theorem eq_of_succ_nsmul_eq (m : ℕ) {x y : A}
    (h : (m + 1) • x = (m + 1) • y) : x = y := by
  simp only [← Nat.cast_smul_eq_nsmul ℚ] at h
  have hm : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact smul_right_injective A hm h

private theorem straightening_step {H E F : A}
    (hef : E * F - F * E = H) (hhe : H * E - E * H = 2 • E)
    (hhf : H * F - F * H = -(2 • F)) (m n : ℕ)
    (ih : dividedPower m E * dividedPower n F =
      ∑ k ∈ range (min m n + 1), straighteningSummand H E F m n k) :
    dividedPower (m + 1) E * dividedPower n F =
      ∑ k ∈ range (min (m + 1) n + 1), straighteningSummand H E F (m + 1) n k := by
  apply eq_of_succ_nsmul_eq m
  have hleft :
      (m + 1) • (dividedPower (m + 1) E * dividedPower n F) =
        E * ∑ k ∈ range (min m n + 1), straighteningSummand H E F m n k := by
    rw [succ_nsmul_dividedPower_succ_mul, ih]
  rw [hleft, mul_sum]
  let K := keptStraighteningSummand H E F m n
  let R := raisedStraighteningSummand H E F m n
  let T := fun k ↦ (m + 1) • straighteningSummand H E F (m + 1) n k
  by_cases hmn : m < n
  · have hmin : min m n = m := min_eq_left (Nat.le_of_lt hmn)
    have hminSucc : min (m + 1) n = m + 1 := min_eq_left hmn
    rw [hmin, hminSucc]
    have hcombine :
        ∑ j ∈ range (m + 2), T j = ∑ k ∈ range (m + 1), (K k + R k) := by
      apply sum_range_adjacent_with_zero K R T m
      · exact (keptStraighteningSummand_zero H E F m n).symm
      · intro j hj0 hjm
        exact (kept_add_raised_pred m n j hj0 hjm).symm
      · simp [K, keptStraighteningSummand]
    rw [Finset.smul_sum]
    rw [hcombine]
    apply sum_congr rfl
    intro k hk
    have hkm := mem_range.mp hk
    dsimp only [K, R]
    exact e_mul_straighteningSummand_of_lt hef hhe hhf
      (Nat.le_of_lt_succ hkm) (by omega)
  · have hnm : n ≤ m := by omega
    have hmin : min m n = n := min_eq_right hnm
    have hminSucc : min (m + 1) n = n := min_eq_right (by omega)
    rw [hmin, hminSucc]
    have hcombine :
        ∑ j ∈ range (n + 1), T j = (∑ k ∈ range n, (K k + R k)) + K n := by
      apply sum_range_adjacent_capped K R T n
      · exact (keptStraighteningSummand_zero H E F m n).symm
      · intro j hj0 _hjn
        exact (kept_add_raised_pred m n j hj0 (by omega)).symm
    rw [Finset.smul_sum]
    rw [hcombine, sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro k hk
      have hkn := mem_range.mp hk
      exact e_mul_straighteningSummand_of_lt hef hhe hhf
        (by omega) hkn
    · exact e_mul_straighteningSummand_of_eq hhe hnm rfl

/-- **The rank-one Kostant straightening formula.** If `H`, `E`, and `F` satisfy the `sl₂`
commutator relations in an associative `ℚ`-algebra, then the product of a raising divided power
and a lowering divided power is an integral sum in PBW order `F`, `H`, `E`.

The argument of the Cartan binomial is written as `H - (m + n) + 2 * k`; the natural numbers are
coerced to the algebra, so this is the standard coefficient `(H - m - n + 2k choose k)`. -/
theorem dividedPower_e_mul_dividedPower_f {H E F : A}
    (hef : E * F - F * E = H) (hhe : H * E - E * H = 2 • E)
    (hhf : H * F - F * H = -(2 • F)) (m n : ℕ) :
    dividedPower m E * dividedPower n F =
      ∑ k ∈ range (min m n + 1),
        dividedPower (n - k) F *
          Ring.choose (H - (m + n : ℕ) + (2 * k : ℕ)) k *
            dividedPower (m - k) E := by
  suffices dividedPower m E * dividedPower n F =
      ∑ k ∈ range (min m n + 1), straighteningSummand H E F m n k by
    simpa only [straighteningSummand]
  induction m with
  | zero => simp [straighteningSummand_zero_left]
  | succ m ih => exact straightening_step hef hhe hhf m n ih

section UniversalEnveloping

open _root_.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {h e f : L}

/-- The rank-one Kostant straightening formula in a universal enveloping algebra over `ℚ`,
stated from the three `sl₂` Lie-bracket relations. -/
theorem dividedPower_ι_e_mul_dividedPower_ι_f (hef : ⁅e, f⁆ = h) (hhe : ⁅h, e⁆ = 2 • e)
    (hhf : ⁅h, f⁆ = -(2 • f)) (m n : ℕ) :
    dividedPower m (ι ℚ e) * dividedPower n (ι ℚ f) =
      ∑ k ∈ range (min m n + 1),
        dividedPower (n - k) (ι ℚ f) *
          Ring.choose (ι ℚ h - (m + n : ℕ) + (2 * k : ℕ)) k *
            dividedPower (m - k) (ι ℚ e) := by
  apply dividedPower_e_mul_dividedPower_f
  · simpa only [LieRing.of_associative_ring_bracket, hef] using ((ι ℚ).map_lie e f).symm
  · simpa only [LieRing.of_associative_ring_bracket, hhe, map_nsmul] using
      ((ι ℚ).map_lie h e).symm
  · simpa only [LieRing.of_associative_ring_bracket, hhf, map_neg, map_nsmul] using
      ((ι ℚ).map_lie h f).symm

end UniversalEnveloping

end TauCeti.Sl2
