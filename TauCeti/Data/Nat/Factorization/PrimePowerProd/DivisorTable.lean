/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Factorization.GcdSplit
public import TauCeti.Data.Nat.Factorization.PrimePowerProd.Basic
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# The divisor multiplication table of a prime-power-multiplicative family

Fix a commutative semiring `R` and two block maps `D S : ℕ → ℕ → R`, and assemble each over a
prime factorisation with `TauCeti.Nat.primePowerProd`. Suppose the assembled `D` obeys the
*per-prime* table: for a prime `p` and `r ≤ s`,

`D_{p^r} · D_{p^s} = ∑_{i ≤ r} pⁱ • (S_{pⁱ} · D_{p^{r+s−2i}})`.

Then it obeys the *global* one, over every pair of nonzero arguments at once:

`D_m · D_n = ∑_{d ∣ gcd m n} d • (S_d · D_{mn/d²})`.

## Main results

* `TauCeti.Nat.primePowerProd_mul_eq_sum_divisors_gcd`: the global table, deduced from the
  per-prime one.

The scalars are natural numbers and no subtraction occurs, so a commutative semiring is enough;
the Hecke-ring consumer is a ring and converts to its `ℤ`-scalars at the point of use.

## Relation to Mathlib

Mathlib's `ArithmeticFunction.IsMultiplicative` describes families multiplicative on *coprime*
arguments, and `ArithmeticFunction.mul` gives them a Dirichlet convolution. Neither expresses this
table: the right-hand side is not a convolution of two arithmetic functions — the index `mn/d²` is
quadratic in the divisor, and the `S`-factor is evaluated at `d` while the `D`-factor is evaluated
at `mn/d²`. The statement is also not about a function `ℕ → R` but about the *assembled* family, so
the per-prime table is the input rather than multiplicativity.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3 — Theorem 3.24, whose Hecke-ring instance is the intended consumer.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB), Apache-2.0, Chris Birkbeck, commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
  `projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`,
  section `FormalTable` (lines 186-438). Two differences in the statement: the sum is taken over
  `Nat.divisors` rather than its `Finset.attach`, the summand never inspecting a membership
  proof, and the index is `d ^ 2` rather than the source's `d * d`. The source's `peelProd` is
  this repository's `TauCeti.Nat.primePowerProd`, and the gcd splitting it needs is
  `TauCeti.Data.Nat.Factorization.GcdSplit`.
-/

public section

open Finset

open scoped Pointwise

namespace TauCeti

namespace Nat

/-! ### The index, split at a prime -/

/-- For `m = p^a·m'` and `n = p^b·n'` with `p` dividing neither `m'` nor `n'`, and `d'` a common
divisor of `m'` and `n'` with `j ≤ min a b`:

`mn/(p^j·d')² = p^{min a b + max a b − 2j} · (m'n'/d'²)`,

and those two factors are coprime. -/
private theorem mul_div_sq_eq_pow_mul_of_not_dvd {p a b m' n' m n d' j : ℕ} (hp : p.Prime)
    (hm_eq : m = p ^ a * m') (hn_eq : n = p ^ b * n') (hm' : ¬p ∣ m') (hn' : ¬p ∣ n')
    (hd'm : d' ∣ m') (hd'n : d' ∣ n') (hj : j ≤ min a b) :
    m * n / (p ^ j * d' * (p ^ j * d')) =
        p ^ (min a b + max a b - 2 * j) * (m' * n' / (d' * d')) ∧
      Nat.Coprime (p ^ (min a b + max a b - 2 * j)) (m' * n' / (d' * d')) := by
  have hdd : d' * d' ∣ m' * n' := Nat.mul_dvd_mul hd'm hd'n
  have hr : min a b + max a b - 2 * j = a + b - 2 * j := by rw [min_add_max]
  have hquot : ¬p ∣ m' * n' / (d' * d') := fun h ↦
    hp.not_dvd_mul hm' hn' (h.trans (Nat.div_dvd_of_dvd hdd))
  set r := a + b - 2 * j with hr_def
  refine ⟨hr ▸ ?_, hr ▸ (hp.coprime_iff_not_dvd.2 hquot).pow_left _⟩
  have hab : a + b = 2 * j + r := by omega
  have h1 : m * n = p ^ (a + b) * (m' * n') := by rw [hm_eq, hn_eq, pow_add]; ring
  have h2 : p ^ j * d' * (p ^ j * d') = p ^ (2 * j) * (d' * d') := by rw [two_mul, pow_add]; ring
  rw [h1, h2, hab, pow_add, mul_assoc, Nat.mul_div_mul_left _ _ (pow_pos hp.pos (2 * j)),
    Nat.mul_div_assoc _ hdd]

/-! ### The table -/

section CommSemiring

variable {R : Type*} [CommSemiring R] (D S : ℕ → ℕ → R)

/-- `f_{p^a} · f_{p^b} = f_{p^{min a b}} · f_{p^{max a b}}`: the two prime-power blocks may be
reordered by size. -/
private theorem primePowerProd_prime_pow_mul_min_max (f : ℕ → ℕ → R) (p a b : ℕ) :
    primePowerProd f (p ^ a) * primePowerProd f (p ^ b) =
      primePowerProd f (p ^ min a b) * primePowerProd f (p ^ max a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, mul_comm]

/-- At the divisor `p ^ j · d'` of `gcd m n`, the two summands multiply to the target summand:
`p^j • (S_{p^j}·D_{p^{…}}) * d' • (S_{d'}·D_{m'n'/d'²}) = (p^j·d') • (S_{p^j·d'}·D_{mn/(p^j·d')²})`.
-/
private theorem primePowerProd_smul_mul_smul_of_not_dvd {p a b m' n' m n d' j : ℕ}
    (hp : p.Prime) (hm_eq : m = p ^ a * m') (hn_eq : n = p ^ b * n') (hm' : ¬p ∣ m')
    (hn' : ¬p ∣ n') (hd'g : d' ∣ Nat.gcd m' n') (hj : j ≤ min a b) :
    ((p ^ j : ℕ) • (primePowerProd S (p ^ j) *
        primePowerProd D (p ^ (min a b + max a b - 2 * j)))) *
      ((d' : ℕ) • (primePowerProd S d' * primePowerProd D (m' * n' / (d' * d')))) =
    ((p ^ j * d' : ℕ)) • (primePowerProd S (p ^ j * d') *
      primePowerProd D (m * n / (p ^ j * d' * (p ^ j * d')))) := by
  have hpg : ¬p ∣ Nat.gcd m' n' := fun h ↦ hm' (h.trans (Nat.gcd_dvd_left m' n'))
  obtain ⟨hidx, hcopD⟩ := mul_div_sq_eq_pow_mul_of_not_dvd hp hm_eq hn_eq hm' hn'
    (hd'g.trans (Nat.gcd_dvd_left m' n')) (hd'g.trans (Nat.gcd_dvd_right m' n')) hj
  have hcopS : Nat.Coprime (p ^ j) d' :=
    (hp.coprime_iff_not_dvd.2 fun h ↦ hpg (h.trans hd'g)).pow_left j
  rw [smul_mul_smul_comm, hidx,
    primePowerProd_mul_of_coprime D hcopD fun _ _ _ _ _ ↦ Commute.all _ _,
    primePowerProd_mul_of_coprime S hcopS fun _ _ _ _ _ ↦ Commute.all _ _]
  ring_nf

/-- When `gcd m n = gcd m' n' · p^{min a b}`, the product of the prime-power sum over
`j ≤ min a b` with the divisor sum over `gcd m' n'` is the divisor sum over `gcd m n`. -/
private theorem primePowerProd_sum_mul_sum_eq_sum_divisors {p a b m' n' m n : ℕ} (hp : p.Prime)
    (hm' : ¬p ∣ m') (hn' : ¬p ∣ n') (hm_eq : m = p ^ a * m')
    (hn_eq : n = p ^ b * n') (hgcd : Nat.gcd m n = Nat.gcd m' n' * p ^ min a b) :
    (∑ j ∈ range (min a b + 1), (p ^ j : ℕ) • (primePowerProd S (p ^ j) *
        primePowerProd D (p ^ (min a b + max a b - 2 * j)))) *
      (∑ d ∈ (Nat.gcd m' n').divisors,
        (d : ℕ) • (primePowerProd S d * primePowerProd D (m' * n' / (d * d)))) =
    ∑ d ∈ (Nat.gcd m n).divisors,
      (d : ℕ) • (primePowerProd S d * primePowerProd D (m * n / (d * d))) := by
  have hpg' : ¬p ∣ Nat.gcd m' n' := fun h ↦ hm' (h.trans (Nat.gcd_dvd_left m' n'))
  have hcop : Nat.Coprime (Nat.gcd m' n') (p ^ min a b) :=
    ((hp.coprime_iff_not_dvd.2 hpg').symm).pow_right _
  rw [hgcd, Nat.divisors_mul, Finset.mul_def,
    Finset.sum_image hcop.mul_injOn_divisors, Finset.sum_product, Finset.sum_mul_sum,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun d' hd' ↦ ?_
  rw [Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Nat.mul_comm d' (p ^ j)]
  exact primePowerProd_smul_mul_smul_of_not_dvd D S hp hm_eq hn_eq hm' hn'
    (Nat.dvd_of_mem_divisors hd') (Finset.mem_range_succ_iff.1 hj)

/-- **The divisor multiplication table.** A family assembled over prime factorisations obeying the
per-prime table `D_{p^r}·D_{p^s} = ∑_{i ≤ r} pⁱ • (S_{pⁱ}·D_{p^{r+s−2i}})` obeys the global one

`D_m · D_n = ∑_{d ∣ gcd m n} d • (S_d · D_{mn/d²})`.

Both arguments must be nonzero: `primePowerProd` sends `0` to the empty product, and `gcd 0 0 = 0`
has no divisors, so at `m = n = 0` the left side is `1` and the right an empty sum. -/
theorem primePowerProd_mul_eq_sum_divisors_gcd
    (hppow : ∀ p : ℕ, p.Prime → ∀ r s : ℕ, r ≤ s →
      primePowerProd D (p ^ r) * primePowerProd D (p ^ s) =
        ∑ i ∈ range (r + 1), (p ^ i : ℕ) • (primePowerProd S (p ^ i) *
          primePowerProd D (p ^ (r + s - 2 * i))))
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    primePowerProd D m * primePowerProd D n =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (d : ℕ) • (primePowerProd S d * primePowerProd D (m * n / d ^ 2)) := by
  simp only [sq]
  induction hg : Nat.gcd m n using Nat.strong_induction_on generalizing m n with
  | _ g ih =>
  rcases eq_or_ne g 1 with rfl | hg1
  · rw [Nat.divisors_one, Finset.sum_singleton, one_smul, Nat.one_mul,
      Nat.div_one, primePowerProd_one, one_mul,
      ← primePowerProd_mul_of_coprime D hg fun _ _ _ _ _ ↦ Commute.all _ _]
  -- Split both arguments at the least prime `p` of the gcd.
  have hg0 : g ≠ 0 := fun h ↦ hm (Nat.eq_zero_of_gcd_eq_zero_left (hg.trans h))
  set p := g.minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime hg1
  have hpm : p ∣ m := (Nat.minFac_dvd g).trans (hg ▸ Nat.gcd_dvd_left m n)
  have hpn : p ∣ n := (Nat.minFac_dvd g).trans (hg ▸ Nat.gcd_dvd_right m n)
  have hm'0 : ordCompl[p] m ≠ 0 := (Nat.ordCompl_pos p hm).ne'
  have hn'0 : ordCompl[p] n ≠ 0 := (Nat.ordCompl_pos p hn).ne'
  have hm' : ¬p ∣ ordCompl[p] m := Nat.not_dvd_ordCompl hp hm
  have hn' : ¬p ∣ ordCompl[p] n := Nat.not_dvd_ordCompl hp hn
  have hm_eq : m = p ^ m.factorization p * ordCompl[p] m :=
    (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hn_eq : n = p ^ n.factorization p * ordCompl[p] n :=
    (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hgcd := gcd_eq_gcd_ordCompl_mul_pow_min (p := p) hp hm hn
  -- The `p`-free gcd is strictly smaller, so the induction hypothesis applies to it.
  have hlt : Nat.gcd (ordCompl[p] m) (ordCompl[p] n) < g := by
    rw [← hg]; exact gcd_ordCompl_lt hp hm hn hpm hpn
  rw [← hg, primePowerProd_eq_ordProj_mul_ordCompl D hp hm,
    primePowerProd_eq_ordProj_mul_ordCompl D hp hn, mul_mul_mul_comm,
    primePowerProd_prime_pow_mul_min_max D p _ _, hppow p hp _ _ min_le_max,
    ih _ hlt hm'0 hn'0 rfl]
  exact primePowerProd_sum_mul_sum_eq_sum_divisors D S hp hm' hn' hm_eq hn_eq hgcd

end CommSemiring

end Nat

end TauCeti
