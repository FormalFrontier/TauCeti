/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Splitting a gcd at a prime

Write two natural numbers as `p ^ a * m'` and `p ^ b * n'` with `p` dividing neither `m'` nor
`n'`. Their gcd then splits into the gcd of the `p`-free parts times `p` to the smaller of the
two exponents:

`gcd (p^a·m') (p^b·n') = gcd m' n' · p ^ min a b`.

`TauCeti.Nat.gcd_pow_mul_pow_mul` is that statement for an arbitrary such splitting, and
`TauCeti.Nat.gcd_eq_gcd_ordCompl_mul_pow_min` is its canonical instance, where the splitting is
the one `Nat.ordProj` and `Nat.ordCompl` perform. `TauCeti.Nat.gcd_ordCompl_lt` draws the
consequence that lets an induction on the gcd terminate: when `p` divides both arguments,
passing to the `p`-free parts strictly shrinks the gcd.

## Main results

* `TauCeti.Nat.gcd_pow_mul_pow_mul`: the gcd splits at a prime, for an explicit splitting.
* `TauCeti.Nat.gcd_eq_gcd_ordCompl_mul_pow_min`: the same for the `ordProj`/`ordCompl` splitting.
* `TauCeti.Nat.gcd_ordCompl_lt`: removing the `p`-part strictly shrinks the gcd.
-/

public section

namespace TauCeti

namespace Nat

/-- **The gcd splits at a prime.** If `p` divides neither `m'` nor `n'`, then the `p`-free part of
`gcd (p^a·m') (p^b·n')` is `gcd m' n'` and its `p`-part is `p ^ min a b`.

No positivity is asked of `m'` or `n'`: `¬p ∣ m'` already forces `m' ≠ 0`, since every prime
divides `0`. -/
theorem gcd_pow_mul_pow_mul {p a b m' n' : ℕ} (hp : p.Prime) (hm' : ¬p ∣ m')
    (hn' : ¬p ∣ n') :
    Nat.gcd (p ^ a * m') (p ^ b * n') = Nat.gcd m' n' * p ^ min a b := by
  have hpa_m' : Nat.Coprime (p ^ a) m' := (hp.coprime_iff_not_dvd.2 hm').pow_left a
  have hpa_n' : Nat.Coprime (p ^ a) n' := (hp.coprime_iff_not_dvd.2 hn').pow_left a
  have hm'_pb : Nat.Coprime m' (p ^ b) := ((hp.coprime_iff_not_dvd.2 hm').pow_left b).symm
  have hgcd_pp : Nat.gcd (p ^ a) (p ^ b) = p ^ min a b := by
    rcases le_total a b with h | h
    · rw [Nat.gcd_eq_left (pow_dvd_pow p h), min_eq_left h]
    · rw [Nat.gcd_eq_right (pow_dvd_pow p h), min_eq_right h]
  rw [hpa_m'.mul_gcd, Nat.Coprime.gcd_mul_right_cancel_right _ hpa_n'.symm,
    Nat.Coprime.gcd_mul_left_cancel_right _ hm'_pb.symm, hgcd_pp, mul_comm]

/-- **The gcd splits at a prime, canonically**:

`gcd m n = gcd (ordCompl[p] m) (ordCompl[p] n) · p ^ min (v_p m) (v_p n)`

for nonzero `m` and `n` — the gcd of the `p`-free parts, times `p` to the smaller of the two
`p`-adic valuations. -/
theorem gcd_eq_gcd_ordCompl_mul_pow_min {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hn : n ≠ 0) :
    Nat.gcd m n = Nat.gcd (ordCompl[p] m) (ordCompl[p] n) *
      p ^ min (m.factorization p) (n.factorization p) := by
  have hm_eq : m = p ^ m.factorization p * ordCompl[p] m :=
    (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hn_eq : n = p ^ n.factorization p * ordCompl[p] n :=
    (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  conv_lhs => rw [hm_eq, hn_eq]
  exact gcd_pow_mul_pow_mul hp (Nat.not_dvd_ordCompl hp hm) (Nat.not_dvd_ordCompl hp hn)

/-- **Removing the `p`-part strictly shrinks the gcd**, when `p` divides both arguments:

`gcd (ordCompl[p] m) (ordCompl[p] n) < gcd m n`.

This is what lets an induction along `TauCeti.Nat.gcd_eq_gcd_ordCompl_mul_pow_min` terminate. -/
theorem gcd_ordCompl_lt {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0)
    (hpm : p ∣ m) (hpn : p ∣ n) :
    Nat.gcd (ordCompl[p] m) (ordCompl[p] n) < Nat.gcd m n := by
  rw [gcd_eq_gcd_ordCompl_mul_pow_min hp hm hn]
  refine lt_mul_of_one_lt_right (Nat.pos_of_ne_zero fun h ↦
    (Nat.ordCompl_pos p hm).ne' (Nat.eq_zero_of_gcd_eq_zero_left h)) (Nat.one_lt_pow ?_ hp.one_lt)
  have ha : 0 < m.factorization p := hp.factorization_pos_of_dvd hm hpm
  have hb : 0 < n.factorization p := hp.factorization_pos_of_dvd hn hpn
  omega

end Nat

end TauCeti

end
