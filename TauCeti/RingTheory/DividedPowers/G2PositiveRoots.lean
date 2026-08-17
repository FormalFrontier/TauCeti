/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.NormalOrdering
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Normal ordering divided powers along the positive `G₂` roots

Let `x`, `y`, `z`, `w`, `v`, and `s` belong to an associative algebra over `ℚ`.  They stand for
root vectors of the six positive `G₂` roots,

```text
x ↔ α,   y ↔ β,   z ↔ α + β,   w ↔ 2α + β,   v ↔ 3α + β,   s ↔ 3α + 2β,
```

normalized so that

```text
x y = y x + z,    x z = z x + 2w,    x w = w x + 3v,    w z = z w + 3s.
```

Besides these four relations only some of the commutations are assumed: `x` with `v` and `s`,
`y` with `z`, `w` with `v` and `s`, `z` with `s`, and `v` with `s`.  Nothing at all is assumed
about the pairs `y, w`, `y, v`, `y, s` and `z, v`.  In particular `y` and `v` do *not* commute in
`G₂`, where `β + (3α + β) = 3α + 2β` is again a root; the straightening rule does not need that
relation.

Under those hypotheses the divided powers have the coefficient-one straightening rule

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ y⁽ᵃ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ v⁽ᵈ⁾ s⁽ᵉ⁾ x⁽ᵐ⁻ᵇ⁻²ᶜ⁻³ᵈ⁻³ᵉ⁾,
```

where `a = n - b - c - d - 2e`.  In particular, all coefficients are integral.  This is the
algebraic input needed to prove the `G₂` Chevalley commutator relation for Kostant root subgroups
over rings of arbitrary characteristic.

The term at `3α + 2β` is essential.  It arises when `x` crosses a divided power of `z`: the
failure of `z` and `w` to commute contributes `3s`.  The four ways to advance the divided-power
series have coefficients `b`, `2c`, `3d`, and `3e`, whose sum is its weighted degree.

The proof feeds `TauCeti.Associative.dividedPower_mul_of_ad_dividedPower_series` the sequence

```text
k ↦ ∑ b + 2c + 3d + 3e = k,  y⁽ᵃ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ v⁽ᵈ⁾ s⁽ᵉ⁾,
```

which is the `k`-th divided power of the inner derivation `ad x` applied to `y⁽ⁿ⁾`.  That is the
plan already used for the chain `β`, `α + β`, `2α + β` in
`TauCeti/RingTheory/DividedPowers/RootString.lean`, with two more exponents to carry; the rule
proved there is the degenerate case `v = s = 0` of the one proved here, and is derived from it.

## Main declarations

* `TauCeti.Associative.g2PositiveRootIndex`: the exponent set in the `G₂` straightening rule.
* `TauCeti.Associative.dividedPower_mul_dividedPower_of_g2PositiveRoots`: coefficient-one normal
  ordering along the positive `G₂` roots.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

open Finset

variable {A : Type*} [Semiring A] [Algebra ℚ A]
variable {x y z w v s : A}

/-! ## Moving one element across a normal-ordered monomial -/

-- The ordinary-power calculation behind the second-order correction when `x` crosses `zⁿ`.
private theorem mul_pow_of_commutator_eq_two_nsmul (hxz : x * z = z * x + 2 • w)
    (hwz : w * z = z * w + 3 • s) (hzs : Commute z s) (n : ℕ) :
    x * z ^ n = z ^ n * x + (2 * (n : ℚ)) • (z ^ (n - 1) * w) +
      (3 * (n : ℚ) * (n - 1 : ℕ)) • (z ^ (n - 2) * s) := by
  have hxzQ : x * z = z * x + (2 : ℚ) • w := by
    simpa only [Algebra.smul_def, map_ofNat, nsmul_eq_mul] using hxz
  have hwzQ : w * z = z * w + (3 : ℚ) • s := by
    simpa only [Algebra.smul_def, map_ofNat, nsmul_eq_mul] using hwz
  induction n with
  | zero => simp
  | succ n ih =>
      rcases n with _ | n
      · simpa using hxzQ
      · simp only [Nat.add_sub_cancel] at ih ⊢
        have hsub : n + 1 - 2 = n - 1 := by omega
        have hsub' : n + 1 + 1 - 2 = n := by omega
        have hs_term : ((3 : ℚ) * (n + 1 : ℕ) * (n : ℚ)) •
            (z ^ (n - 1) * s * z) =
          ((3 : ℚ) * (n + 1 : ℕ) * (n : ℚ)) • (z ^ n * s) := by
          cases n with
          | zero => simp
          | succ n =>
              simp only [Nat.add_sub_cancel]
              congr 1
              rw [mul_assoc, hzs.eq.symm, ← mul_assoc, ← pow_succ]
        rw [pow_succ, ← mul_assoc, ih, add_mul, add_mul, mul_assoc (z ^ (n + 1)) x z,
          hxzQ, mul_add, smul_mul_assoc, mul_assoc (z ^ n) w z, hwzQ,
          mul_add (z ^ n) (z * w) ((3 : ℚ) • s),
          smul_add, smul_mul_assoc, hsub]
        rw [hs_term, hsub']
        simp only [Nat.cast_add, Nat.cast_one, Algebra.smul_def,
          map_add, map_mul, map_natCast, map_ofNat, map_one]
        noncomm_ring [pow_succ]

-- Dividing the preceding identity by `(n + 2)!` gives coefficients `2` and `3`.
private theorem mul_dividedPower_z_succ_succ (hxz : x * z = z * x + 2 • w)
    (hwz : w * z = z * w + 3 • s) (hzs : Commute z s) (n : ℕ) :
    x * dividedPower (n + 2) z =
      dividedPower (n + 2) z * x +
        2 • (dividedPower (n + 1) z * w) + 3 • (dividedPower n z * s) := by
  simp only [dividedPower_def, mul_smul_comm, smul_mul_assoc]
  rw [mul_pow_of_commutator_eq_two_nsmul hxz hwz hzs]
  have h1 : n + 2 - 1 = n + 1 := by omega
  have h2 : n + 2 - 2 = n := by omega
  rw [h1, h2]
  simp only [smul_add]
  congr 1
  · congr 1
    simp_rw [← Nat.cast_smul_eq_nsmul ℚ]
    simp only [smul_smul]
    congr 1
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
  · simp_rw [← Nat.cast_smul_eq_nsmul ℚ]
    simp only [smul_smul]
    congr 1
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp

private theorem mul_dividedPower_z (hxz : x * z = z * x + 2 • w)
    (hwz : w * z = z * w + 3 • s) (hzs : Commute z s) (n : ℕ) :
    x * dividedPower n z = dividedPower n z * x +
        (if 0 < n then 2 • (dividedPower (n - 1) z * w) else 0) +
        (if 1 < n then 3 • (dividedPower (n - 2) z * s) else 0) := by
  rcases n with _ | _ | n
  · simp
  · simp only [dividedPower_one, Nat.zero_lt_succ, ↓reduceIte, Nat.reduceLT, zero_add,
      add_zero]
    rw [show 1 - 1 = 0 by omega, dividedPower_zero, one_mul]
    exact hxz
  · simp only [ite_eq_left (by omega : 0 < n + 1 + 1),
      ite_eq_left (by omega : 1 < n + 1 + 1)]
    have h1 : n + 1 + 1 - 1 = n + 1 := by omega
    have h2 : n + 1 + 1 - 2 = n := by omega
    rw [h1, h2]
    exact mul_dividedPower_z_succ_succ hxz hwz hzs n

-- Multiplication by `x` advances one of the four non-simple-root exponents.  The last summand
-- trades two `z` factors for one `s` factor and is the feature absent from shorter root strings.
private theorem mul_dividedPower_g2Monomial
    (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z)
    (hwv : Commute w v) (hzs : Commute z s) (hws : Commute w s)
    (hvs : Commute v s) (a b c d e : ℕ) :
    x * (dividedPower a y * dividedPower b z * dividedPower c w * dividedPower d v *
        dividedPower e s) =
      dividedPower a y * dividedPower b z * dividedPower c w * dividedPower d v *
          dividedPower e s * x +
        (if 0 < a then
          (b + 1) • (dividedPower (a - 1) y * dividedPower (b + 1) z *
            dividedPower c w * dividedPower d v * dividedPower e s) else 0) +
        (if 0 < b then
          (2 * (c + 1)) • (dividedPower a y * dividedPower (b - 1) z *
            dividedPower (c + 1) w * dividedPower d v * dividedPower e s) else 0) +
        (if 0 < c then
          (3 * (d + 1)) • (dividedPower a y * dividedPower b z *
            dividedPower (c - 1) w * dividedPower (d + 1) v * dividedPower e s) else 0) +
        (if 1 < b then
          (3 * (e + 1)) • (dividedPower a y * dividedPower (b - 2) z *
            dividedPower c w * dividedPower d v * dividedPower (e + 1) s) else 0) := by
  have hxvd : Commute x (dividedPower d v) := by
    simpa using commute_dividedPower_dividedPower hxv 1 d
  have hxse : Commute x (dividedPower e s) := by
    simpa using commute_dividedPower_dividedPower hxs 1 e
  have hwv3 : Commute w (3 • v) := hwv.smul_right 3
  have hy := mul_dividedPower_of_commutator_eq' hxy hyz a
  have hz := mul_dividedPower_z hxz hwz hzs b
  have hw := mul_dividedPower_of_commutator_eq' hxw hwv3 c
  have hw' : x * dividedPower c w = dividedPower c w * x +
      if 0 < c then 3 • (dividedPower (c - 1) w * v) else 0 := by
    rw [hw]
    split_ifs
    · rw [mul_smul_comm]
    · rfl
  -- Split the product into the ordered term and the four released commutator terms, keeping the
  -- latter unevaluated: `y → z` from `hy`, then `z → w` and `z + z → s` from `hz`, then
  -- `w → v` from `hw'`.  The four `have`s below absorb each released factor into the divided
  -- power it lengthens.
  have hsplit : x * (dividedPower a y * dividedPower b z * dividedPower c w *
        dividedPower d v * dividedPower e s) =
      dividedPower a y * dividedPower b z * dividedPower c w * dividedPower d v *
          dividedPower e s * x +
        (if 0 < a then dividedPower (a - 1) y * z else 0) * dividedPower b z *
          dividedPower c w * dividedPower d v * dividedPower e s +
        dividedPower a y * (if 0 < b then 2 • (dividedPower (b - 1) z * w) else 0) *
        dividedPower c w * dividedPower d v * dividedPower e s +
        dividedPower a y * dividedPower b z *
          (if 0 < c then dividedPower (c - 1) w * (3 • v) else 0) *
          dividedPower d v * dividedPower e s +
        dividedPower a y * (if 1 < b then 3 • (dividedPower (b - 2) z * s) else 0) *
          dividedPower c w * dividedPower d v * dividedPower e s := by
    calc
      x * (dividedPower a y * dividedPower b z * dividedPower c w * dividedPower d v *
          dividedPower e s) =
          (x * dividedPower a y) * dividedPower b z * dividedPower c w *
            dividedPower d v * dividedPower e s := by simp only [mul_assoc]
      _ = _ := by
        rw [hy]
        noncomm_ring [hz, hw', hxvd.eq, hxse.eq]
  have hYtoZ : (if 0 < a then dividedPower (a - 1) y * z else 0) * dividedPower b z *
        dividedPower c w * dividedPower d v * dividedPower e s =
      if 0 < a then (b + 1) • (dividedPower (a - 1) y * dividedPower (b + 1) z *
        dividedPower c w * dividedPower d v * dividedPower e s) else 0 := by
    split_ifs with ha
    · rw [mul_assoc (dividedPower (a - 1) y) z, self_mul_dividedPower,
        mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
    · simp
  have hZtoW : dividedPower a y *
        (if 0 < b then 2 • (dividedPower (b - 1) z * w) else 0) *
        dividedPower c w * dividedPower d v * dividedPower e s =
      if 0 < b then (2 * (c + 1)) • (dividedPower a y * dividedPower (b - 1) z *
        dividedPower (c + 1) w * dividedPower d v * dividedPower e s) else 0 := by
    split_ifs with hb
    · have hmul := self_mul_dividedPower (x := w) c
      noncomm_ring [hmul]
      module
    · simp
  have hWtoV : dividedPower a y * dividedPower b z *
        (if 0 < c then dividedPower (c - 1) w * (3 • v) else 0) *
        dividedPower d v * dividedPower e s =
      if 0 < c then (3 * (d + 1)) • (dividedPower a y * dividedPower b z *
        dividedPower (c - 1) w * dividedPower (d + 1) v * dividedPower e s) else 0 := by
    split_ifs with hc
    · have hmul := self_mul_dividedPower (x := v) d
      noncomm_ring [hmul]
      module
    · simp
  have hZZtoS : dividedPower a y *
        (if 1 < b then 3 • (dividedPower (b - 2) z * s) else 0) *
        dividedPower c w * dividedPower d v * dividedPower e s =
      if 1 < b then (3 * (e + 1)) • (dividedPower a y * dividedPower (b - 2) z *
        dividedPower c w * dividedPower d v * dividedPower (e + 1) s) else 0 := by
    split_ifs with hb
    · have hswc : Commute s (dividedPower c w) := by
        simpa using commute_dividedPower_dividedPower hws.symm 1 c
      have hsvd : Commute s (dividedPower d v) := by
        simpa using commute_dividedPower_dividedPower hvs.symm 1 d
      have hmul := self_mul_dividedPower (x := s) e
      noncomm_ring [hswc.eq, hsvd.eq, hmul]
      module
    · simp
  rw [hsplit, hYtoZ, hZtoW, hWtoV, hZZtoS]

/-! ## The divided-power series of the inner derivation -/

private abbrev G2Exponents := ℕ × ℕ × ℕ × ℕ

private def g2Total (p : G2Exponents) : ℕ :=
  p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2

private def g2Weight (p : G2Exponents) : ℕ :=
  p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2

/-- The exponents in the `k`-th divided power of `ad x` applied to `y⁽ⁿ⁾`. -/
private def g2SeriesIndex (n k : ℕ) : Finset G2Exponents :=
  {p ∈ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) |
    g2Total p ≤ n ∧ g2Weight p = k}

private theorem mem_g2SeriesIndex {n k : ℕ} {p : G2Exponents} :
    p ∈ g2SeriesIndex n k ↔ g2Total p ≤ n ∧ g2Weight p = k := by
  rw [g2SeriesIndex, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    simp only [Finset.mem_product, Finset.mem_range]
    have := h.1
    simp only [g2Total] at this
    omega

private noncomputable def g2Monomial (y z w v s : A) (n : ℕ) (p : G2Exponents) : A :=
  dividedPower (n - g2Total p) y * dividedPower p.1 z * dividedPower p.2.1 w *
    dividedPower p.2.2.1 v * dividedPower p.2.2.2 s

/-- The `k`-th divided power of `ad x`, applied to `y⁽ⁿ⁾`. -/
private noncomputable def g2Series (y z w v s : A) (n k : ℕ) : A :=
  ∑ p ∈ g2SeriesIndex n k, g2Monomial y z w v s n p

private theorem g2Series_zero (n : ℕ) : g2Series y z w v s n 0 = dividedPower n y := by
  have hindex : g2SeriesIndex n 0 = {(0, 0, 0, 0)} := by
    ext ⟨b, c, d, e⟩
    simp only [mem_g2SeriesIndex, Finset.mem_singleton, Prod.mk.injEq, g2Total, g2Weight]
    omega
  rw [g2Series, hindex]
  simp [g2Monomial, g2Total]

/-! ### Reindexing the four exponent shifts

Each of the four ways to advance the series moves the index `p` of weighted degree `k` to an
index of weighted degree `k + 1` by a fixed shift of the exponents.  All four are instances of
one reindexing lemma, which leaves each of them only the arithmetic of its own shift. -/

/-- Membership in a slice of `g2SeriesIndex` cut out by a further predicate, unfolded to the
two degree conditions defining the index set. -/
private theorem mem_filter_g2SeriesIndex {n k : ℕ} {P : G2Exponents → Prop} [DecidablePred P]
    {p : G2Exponents} :
    p ∈ {p ∈ g2SeriesIndex n k | P p} ↔ (g2Total p ≤ n ∧ g2Weight p = k) ∧ P p := by
  rw [Finset.mem_filter, mem_g2SeriesIndex]

/-- The reindexing shared by the four exponent shifts.  A shift `f` with inverse `finv` matches
the indices of weighted degree `k` cut out by `P` with those of weighted degree `k + 1` cut out
by `Q`, and `hval` identifies the summand at `p` with `coeff (f p)` copies of the monomial at
`f p`. -/
private theorem sum_g2Monomial_shift {n k : ℕ} {P Q : G2Exponents → Prop}
    [DecidablePred P] [DecidablePred Q] {F : G2Exponents → A}
    (f finv : G2Exponents → G2Exponents) (coeff : G2Exponents → ℕ)
    (hf : ∀ p, (g2Total p ≤ n ∧ g2Weight p = k) ∧ P p →
      (g2Total (f p) ≤ n ∧ g2Weight (f p) = k + 1) ∧ Q (f p))
    (hfinv : ∀ q, (g2Total q ≤ n ∧ g2Weight q = k + 1) ∧ Q q →
      (g2Total (finv q) ≤ n ∧ g2Weight (finv q) = k) ∧ P (finv q))
    (hleft : ∀ p, (g2Total p ≤ n ∧ g2Weight p = k) ∧ P p → finv (f p) = p)
    (hright : ∀ q, (g2Total q ≤ n ∧ g2Weight q = k + 1) ∧ Q q → f (finv q) = q)
    (hval : ∀ p, (g2Total p ≤ n ∧ g2Weight p = k) ∧ P p →
      F p = coeff (f p) • g2Monomial y z w v s n (f p)) :
    ∑ p ∈ {p ∈ g2SeriesIndex n k | P p}, F p =
      ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | Q q}, coeff q • g2Monomial y z w v s n q :=
  Finset.sum_nbij' f finv
    (fun _ hp => mem_filter_g2SeriesIndex.mpr (hf _ (mem_filter_g2SeriesIndex.mp hp)))
    (fun _ hq => mem_filter_g2SeriesIndex.mpr (hfinv _ (mem_filter_g2SeriesIndex.mp hq)))
    (fun _ hp => hleft _ (mem_filter_g2SeriesIndex.mp hp))
    (fun _ hq => hright _ (mem_filter_g2SeriesIndex.mp hq))
    (fun _ hp => hval _ (mem_filter_g2SeriesIndex.mp hp))

-- The `y → z` advance: one `y` factor is traded for a `z` factor.
private theorem sum_g2Monomial_shift_z (n k : ℕ) :
    ∑ p ∈ {p ∈ g2SeriesIndex n k | 0 < n - g2Total p},
        (p.1 + 1) • (dividedPower (n - g2Total p - 1) y * dividedPower (p.1 + 1) z *
          dividedPower p.2.1 w * dividedPower p.2.2.1 v * dividedPower p.2.2.2 s) =
      ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.1}, q.1 • g2Monomial y z w v s n q := by
  refine sum_g2Monomial_shift (fun p => (p.1 + 1, p.2.1, p.2.2.1, p.2.2.2))
    (fun q => (q.1 - 1, q.2.1, q.2.2.1, q.2.2.2)) (fun q => q.1) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨b, c, d, e⟩ hp
    simp only [g2Total, g2Weight] at hp ⊢
    omega
  · rintro ⟨b, c, d, e⟩ hq
    simp only [g2Total, g2Weight] at hq ⊢
    omega
  · rintro ⟨b, c, d, e⟩ _
    simp
  · rintro ⟨b, c, d, e⟩ hq
    simp [Nat.sub_add_cancel hq.2]
  · rintro ⟨b, c, d, e⟩ _
    simp only [g2Monomial, g2Total]
    have ht : b + c + d + 2 * e + 1 = b + 1 + c + d + 2 * e := by omega
    rw [Nat.sub_sub, ht]

-- The `z → w` advance.
private theorem sum_g2Monomial_shift_w (n k : ℕ) :
    ∑ p ∈ {p ∈ g2SeriesIndex n k | 0 < p.1},
        (2 * (p.2.1 + 1)) • (dividedPower (n - g2Total p) y *
          dividedPower (p.1 - 1) z * dividedPower (p.2.1 + 1) w *
            dividedPower p.2.2.1 v * dividedPower p.2.2.2 s) =
      ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.1},
        (2 * q.2.1) • g2Monomial y z w v s n q := by
  refine sum_g2Monomial_shift (fun p => (p.1 - 1, p.2.1 + 1, p.2.2.1, p.2.2.2))
    (fun q => (q.1 + 1, q.2.1 - 1, q.2.2.1, q.2.2.2)) (fun q => 2 * q.2.1) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨b, c, d, e⟩ hp
    simp only [g2Total, g2Weight] at hp ⊢
    omega
  · rintro ⟨b, c, d, e⟩ hq
    simp only [g2Total, g2Weight] at hq ⊢
    omega
  · rintro ⟨b, c, d, e⟩ hp
    simp [Nat.sub_add_cancel hp.2]
  · rintro ⟨b, c, d, e⟩ hq
    simp [Nat.sub_add_cancel hq.2]
  · rintro ⟨b, c, d, e⟩ hp
    have hb : 0 < b := hp.2
    simp only [g2Monomial, g2Total]
    have ht : b - 1 + (c + 1) + d + 2 * e = b + c + d + 2 * e := by omega
    rw [ht]

-- The `w → v` advance.
private theorem sum_g2Monomial_shift_v (n k : ℕ) :
    ∑ p ∈ {p ∈ g2SeriesIndex n k | 0 < p.2.1},
        (3 * (p.2.2.1 + 1)) • (dividedPower (n - g2Total p) y * dividedPower p.1 z *
          dividedPower (p.2.1 - 1) w * dividedPower (p.2.2.1 + 1) v *
            dividedPower p.2.2.2 s) =
      ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.2.1},
        (3 * q.2.2.1) • g2Monomial y z w v s n q := by
  refine sum_g2Monomial_shift (fun p => (p.1, p.2.1 - 1, p.2.2.1 + 1, p.2.2.2))
    (fun q => (q.1, q.2.1 + 1, q.2.2.1 - 1, q.2.2.2)) (fun q => 3 * q.2.2.1) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨b, c, d, e⟩ hp
    simp only [g2Total, g2Weight] at hp ⊢
    omega
  · rintro ⟨b, c, d, e⟩ hq
    simp only [g2Total, g2Weight] at hq ⊢
    omega
  · rintro ⟨b, c, d, e⟩ hp
    simp [Nat.sub_add_cancel hp.2]
  · rintro ⟨b, c, d, e⟩ hq
    simp [Nat.sub_add_cancel hq.2]
  · rintro ⟨b, c, d, e⟩ hp
    have hc : 0 < c := hp.2
    simp only [g2Monomial, g2Total]
    have ht : b + (c - 1) + (d + 1) + 2 * e = b + c + d + 2 * e := by omega
    rw [ht]

-- The `z + z → s` advance, the step absent from shorter root strings.
private theorem sum_g2Monomial_shift_s (n k : ℕ) :
    ∑ p ∈ {p ∈ g2SeriesIndex n k | 1 < p.1},
        (3 * (p.2.2.2 + 1)) • (dividedPower (n - g2Total p) y *
          dividedPower (p.1 - 2) z * dividedPower p.2.1 w * dividedPower p.2.2.1 v *
            dividedPower (p.2.2.2 + 1) s) =
      ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.2.2},
        (3 * q.2.2.2) • g2Monomial y z w v s n q := by
  refine sum_g2Monomial_shift (fun p => (p.1 - 2, p.2.1, p.2.2.1, p.2.2.2 + 1))
    (fun q => (q.1 + 2, q.2.1, q.2.2.1, q.2.2.2 - 1)) (fun q => 3 * q.2.2.2) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨b, c, d, e⟩ hp
    simp only [g2Total, g2Weight] at hp ⊢
    omega
  · rintro ⟨b, c, d, e⟩ hq
    simp only [g2Total, g2Weight] at hq ⊢
    omega
  · rintro ⟨b, c, d, e⟩ hp
    have hb : 1 < b := hp.2
    simp [Nat.sub_add_cancel (show 2 ≤ b by omega)]
  · rintro ⟨b, c, d, e⟩ hq
    simp [Nat.sub_add_cancel hq.2]
  · rintro ⟨b, c, d, e⟩ hp
    have hb : 1 < b := hp.2
    simp only [g2Monomial, g2Total]
    have ht : b - 2 + c + d + 2 * (e + 1) = b + c + d + 2 * e := by omega
    rw [ht]

-- The four advances weight an index `q` by its four exponents, and those weights sum to the
-- weighted degree `k + 1`.
private theorem nsmul_g2Series_succ (n k : ℕ) :
    (k + 1) • g2Series y z w v s n (k + 1) =
      (∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.1},
          q.1 • g2Monomial y z w v s n q) +
        (∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.1},
          (2 * q.2.1) • g2Monomial y z w v s n q) +
        (∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.2.1},
          (3 * q.2.2.1) • g2Monomial y z w v s n q) +
        (∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.2.2},
          (3 * q.2.2.2) • g2Monomial y z w v s n q) := by
  symm
  rw [Finset.sum_filter_of_ne
      (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
    Finset.sum_filter_of_ne
      (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
    Finset.sum_filter_of_ne
      (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
    Finset.sum_filter_of_ne
      (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
    g2Series, Finset.smul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [← add_smul, ← add_smul, ← add_smul]
  congr 1
  have hwgt := (mem_g2SeriesIndex.mp hq).2
  simp only [g2Weight] at hwgt
  omega

-- Multiplication by `x` advances the series in weighted degree.  The four possible advances are
-- respectively `y → z`, `z → w`, `w → v`, and `z + z → s`.
private theorem mul_g2Series
    (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z)
    (hwv : Commute w v) (hzs : Commute z s) (hws : Commute w s)
    (hvs : Commute v s) (n k : ℕ) :
    x * g2Series y z w v s n k =
      g2Series y z w v s n k * x + (k + 1) • g2Series y z w v s n (k + 1) := by
  classical
  have hterm : ∀ p ∈ g2SeriesIndex n k,
      x * g2Monomial y z w v s n p = g2Monomial y z w v s n p * x +
        (if 0 < n - g2Total p then
          (p.1 + 1) • (dividedPower (n - g2Total p - 1) y *
            dividedPower (p.1 + 1) z * dividedPower p.2.1 w * dividedPower p.2.2.1 v *
              dividedPower p.2.2.2 s)
          else 0) +
        (if 0 < p.1 then
          (2 * (p.2.1 + 1)) • (dividedPower (n - g2Total p) y *
            dividedPower (p.1 - 1) z * dividedPower (p.2.1 + 1) w *
              dividedPower p.2.2.1 v * dividedPower p.2.2.2 s)
          else 0) +
        (if 0 < p.2.1 then
          (3 * (p.2.2.1 + 1)) • (dividedPower (n - g2Total p) y *
            dividedPower p.1 z * dividedPower (p.2.1 - 1) w *
              dividedPower (p.2.2.1 + 1) v * dividedPower p.2.2.2 s)
          else 0) +
        (if 1 < p.1 then
          (3 * (p.2.2.2 + 1)) • (dividedPower (n - g2Total p) y *
            dividedPower (p.1 - 2) z * dividedPower p.2.1 w * dividedPower p.2.2.1 v *
              dividedPower (p.2.2.2 + 1) s)
          else 0) := by
    intro p hp
    rw [g2Monomial,
      mul_dividedPower_g2Monomial hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs]
  rw [g2Series, Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.sum_filter, ← Finset.sum_filter, sum_g2Monomial_shift_z,
    sum_g2Monomial_shift_w, sum_g2Monomial_shift_v, sum_g2Monomial_shift_s,
    nsmul_g2Series_succ]
  abel

/-! ## The straightening rule -/

/-- The quadruples `(b, c, d, e)` of non-simple-root exponents in the `G₂` straightening
rule.  The two inequalities record respectively the total `y`-degree used and the weighted
`x`-degree used. -/
def g2PositiveRootIndex (m n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {p ∈ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) |
    p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2 ≤ n ∧
      p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2 ≤ m}

/-- Membership in `g2PositiveRootIndex` in terms of its two degree inequalities. -/
@[simp]
theorem mem_g2PositiveRootIndex {m n : ℕ} {p : ℕ × ℕ × ℕ × ℕ} :
    p ∈ g2PositiveRootIndex m n ↔
      p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2 ≤ n ∧
        p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2 ≤ m := by
  rw [g2PositiveRootIndex, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    simp only [Finset.mem_product, Finset.mem_range]
    omega

/-- **Coefficient-one normal ordering along the positive `G₂` roots.** Suppose

```text
x y = y x + z,   x z = z x + 2w,   x w = w x + 3v,   w z = z w + 3s,
```

that `x` commutes with `v` and with `s`, that `y` commutes with `z`, that `w` commutes with `v`
and with `s`, that `z` commutes with `s`, and that `v` commutes with `s`. Nothing is assumed
about the pairs `y, w`, `y, v`, `y, s` and `z, v`; in particular the `G₂` relation between the
root vectors of `β` and `3α + β`, whose sum `3α + 2β` is again a root, is not needed. Then

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ y⁽ⁿ⁻ᵇ⁻ᶜ⁻ᵈ⁻²ᵉ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ v⁽ᵈ⁾ s⁽ᵉ⁾ x⁽ᵐ⁻ᵇ⁻²ᶜ⁻³ᵈ⁻³ᵉ⁾.
```

The sum is over `g2PositiveRootIndex m n`. Every coefficient in the divided-power basis is `1`,
so this identity supplies the integral straightening input for the `G₂` Chevalley commutator
relation. Setting `v = s = 0` and discarding the terms with `d ≠ 0` or `e ≠ 0` recovers the
chain rule `dividedPower_mul_dividedPower_of_commutator_eq_two_nsmul`, which is derived from
this theorem in `TauCeti/RingTheory/DividedPowers/RootString.lean`. -/
theorem dividedPower_mul_dividedPower_of_g2PositiveRoots
    (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z)
    (hwv : Commute w v) (hzs : Commute z s) (hws : Commute w s)
    (hvs : Commute v s) (m n : ℕ) :
    dividedPower m x * dividedPower n y =
      ∑ p ∈ g2PositiveRootIndex m n,
        dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) y *
          dividedPower p.1 z * dividedPower p.2.1 w * dividedPower p.2.2.1 v *
            dividedPower p.2.2.2 s *
          dividedPower (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) x := by
  classical
  set S : Finset G2Exponents := g2PositiveRootIndex m n with hS
  have hmemS : ∀ p : G2Exponents, p ∈ S ↔ g2Total p ≤ n ∧ g2Weight p ≤ m := by
    intro p
    simpa only [hS, g2Total, g2Weight] using
      (mem_g2PositiveRootIndex (m := m) (n := n) (p := p))
  have hseries := dividedPower_mul_of_ad_dividedPower_series
    (x := x) (d := g2Series y z w v s n)
    (fun k => mul_g2Series hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs n k) m
  rw [g2Series_zero] at hseries
  rw [hseries]
  trans ∑ p ∈ S, g2Monomial y z w v s n p * dividedPower (m - g2Weight p) x
  · rw [← Finset.sum_fiberwise_of_maps_to (g := g2Weight) (t := range (m + 1))
      (fun p hp => Finset.mem_range.mpr (by have := (hmemS p).mp hp; omega))
      (fun p => g2Monomial y z w v s n p * dividedPower (m - g2Weight p) x)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hfib : {p ∈ S | g2Weight p = k} = g2SeriesIndex n k := by
      ext p
      simp only [Finset.mem_filter, hmemS, mem_g2SeriesIndex]
      omega
    rw [hfib, g2Series, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(mem_g2SeriesIndex.mp hp).2]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hyexp : n - g2Total p = n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2 := by
      simp only [g2Total]
      omega
    have hxexp : m - g2Weight p =
        m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2 := by
      simp only [g2Weight]
      omega
    rw [g2Monomial]
    rw [hyexp, hxexp]

end TauCeti.Associative
