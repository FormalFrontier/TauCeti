/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.Prime.Pow

/-!
# Ordered products over a prime factorisation

`n.factorization.prod f` multiplies the blocks `f p (n.factorization p)` over the primes
dividing `n`. Being a `Finsupp.prod` it asks for a `CommMonoid`: a `Finsupp` records no order
on its support, so the product is only well defined once the factors commute.

`TauCeti.Nat.primePowerProd f n` multiplies the same blocks in a fixed order — least prime
first — and so asks only for `One` and `Mul`. Each step peels `Nat.minFac n` together with its
whole multiplicity, and recurses on `ordCompl[n.minFac] n`. Both `n = 0` and `n = 1` give the
empty product.

The ordering is not the point; the weakened typeclass is. A monoid that happens to be
commutative without carrying a `CommMonoid` *instance* — a Hecke ring whose commutativity is a
theorem rather than a structure field, say — cannot form `n.factorization.prod f` at all, and
this is what it forms instead. `primePowerProd_eq_factorization_prod` records that nothing is
lost: as soon as a `CommMonoid` instance is available the two agree.

Neither associativity nor a unit law enters the definition — the bracketing is fixed — so it is
stated at `One` plus `Mul`, in the same spirit as `List.prod`, which Lean defines at `Mul` plus
`One`. `mul_one` is needed once, to collapse the single block of a prime power. Associativity
enters with the multiplicativity on coprime arguments, which is stated in a `Monoid` under the
hypothesis it actually uses — each block of `n` commutes with the blocks of `m` at larger primes,
the pairs that merging the two increasing sequences has to exchange — so that the monoid of the
previous paragraph can use it. Only the `Finsupp.prod` comparison needs the full `CommMonoid`.

## Main definitions

* `TauCeti.Nat.primePowerProd`: the product of `f p (n.factorization p)` over the primes of
  `n`, taken in increasing order of prime.

## Main results

* `TauCeti.Nat.primePowerProd_of_one_lt`: the peeling step, as a rewriting rule.
* `TauCeti.Nat.primePowerProd_prime_pow`: on a prime power the product is a single block;
  `TauCeti.Nat.primePowerProd_prime` is the same at a bare prime.
* `Commute.primePowerProd_right`: an element commuting with every block commutes with the
  ordered product.
* `TauCeti.Nat.primePowerProd_mul_of_coprime`: multiplicativity on coprime arguments, given
  that each block of `n` commutes with the blocks of `m` at larger primes.
* `TauCeti.Nat.primePowerProd_eq_factorization_prod`: in a `CommMonoid` it is
  `n.factorization.prod f`.

## Implementation notes

The definition is `Nat.recOnPrimePow`, which already performs the least-prime-power
decomposition this product runs over. That recursor is `@[elab_as_elim]` and mathlib states no
computation rules for it, so the three equations `primePowerProd_zero`, `primePowerProd_one`
and `primePowerProd_of_one_lt` are proved by unfolding it and `Nat.strongRec` once. Everything
after them goes through those equations and never through the body again.

Coprime multiplicativity is a strong induction on `m * n`. The least prime of `m * n` lies in
exactly one of the factors, and the peeling step splits off its block. When it lies in `m` the
induction hypothesis and the peeling step for `m` already give the answer. When it lies in `n`
its block comes out ahead of the whole of `primePowerProd f m`; it sits below every prime of
`m`, so the commutation hypothesis moves it past that product — the one place the hypothesis is
used — and the peeling step for `n` reassembles `primePowerProd f n`.

## Provenance

Adapted from AINTLIB (see References): `peelProd` and its six companion lemmas, which sit in a
Hecke file inside the `HeckeRing.GL2.Unified` namespace. They are combinatorics about
`Nat.minFac` carrying no Hecke content, so they are lifted here. The source asks
`Monoid`/`CommMonoid` and writes the recursion out by hand; here the classes are weakened to
`One` plus `Mul`, the recursion is routed through mathlib's `Nat.recOnPrimePow`, the coprime
multiplicativity is proved in a `Monoid` from the commutation of the block pairs that merging
exchanges instead of being read off the `Finsupp.prod` comparison, and that comparison is
stated for every `n` rather than only for `n ≠ 0`. The comparison is `private` in the source
and is exposed here, since it is the statement tying the definition to mathlib's idiom.

## References

* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), Apache-2.0, commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`,
  `projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`,
  lines 111-184.
-/

public section

namespace TauCeti

namespace Nat

/-- For `1 < n` the least prime factor of `n` is one of its primes. -/
private theorem minFac_mem_primeFactors {n : ℕ} (hn : 1 < n) : n.minFac ∈ n.primeFactors :=
  Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hn.ne', n.minFac_dvd, by omega⟩

/-- Peeling the block at the least prime factor makes `n` strictly smaller. -/
private theorem ordCompl_minFac_lt {n : ℕ} (hn : 1 < n) : ordCompl[n.minFac] n < n :=
  Nat.div_lt_self (by omega) (Nat.one_lt_pow
    ((Nat.minFac_prime hn.ne').factorization_pos_of_dvd (by omega) n.minFac_dvd).ne'
    (Nat.minFac_prime hn.ne').one_lt)

/-- A block of `ordCompl[p] n` is a block of `n`, at a prime other than `p`. -/
private theorem block_ordCompl {n p q : ℕ} (hq : q ∈ (ordCompl[p] n).primeFactors) :
    q ∈ n.primeFactors ∧ (ordCompl[p] n).factorization q = n.factorization q := by
  rw [← Nat.support_factorization, Nat.factorization_ordCompl, Finsupp.support_erase,
    Finset.mem_erase, Nat.support_factorization] at hq
  exact ⟨hq.2, by rw [Nat.factorization_ordCompl, Finsupp.erase_ne hq.1]⟩

variable {M : Type*}

section MulOne

variable [One M] [Mul M]

/-- The product of the blocks `f p (n.factorization p)` over the primes `p` dividing `n`, taken
in increasing order of `p`: each step peels off the least prime factor of `n` together with its
whole multiplicity. The empty product `1` is returned at `n = 1`, and at `n = 0` as a junk
value — `0` has no factorisation to run over.

Only `One M` and `Mul M` are asked, which is the whole point of the definition; see
`primePowerProd_eq_factorization_prod` for the agreement with `n.factorization.prod f` when `M`
is commutative. -/
noncomputable def primePowerProd (f : ℕ → ℕ → M) : ℕ → M :=
  Nat.recOnPrimePow 1 1 fun _ p v _ _ _ ih ↦ f p v * ih

@[simp]
theorem primePowerProd_zero (f : ℕ → ℕ → M) : primePowerProd f 0 = 1 := by
  unfold primePowerProd Nat.recOnPrimePow
  rw [Nat.strongRec_eq]

@[simp]
theorem primePowerProd_one (f : ℕ → ℕ → M) : primePowerProd f 1 = 1 := by
  unfold primePowerProd Nat.recOnPrimePow
  rw [Nat.strongRec_eq]

/-- **The peeling step**: for `1 < n` the ordered product splits off the block at `n.minFac`,
leaving the ordered product over `ordCompl[n.minFac] n`. -/
theorem primePowerProd_of_one_lt (f : ℕ → ℕ → M) {n : ℕ} (hn : 1 < n) : primePowerProd f n =
    f n.minFac (n.factorization n.minFac) *
      primePowerProd f (n / n.minFac ^ n.factorization n.minFac) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  unfold primePowerProd Nat.recOnPrimePow
  rw [Nat.strongRec_eq]
  rfl

end MulOne

section MulOneClass

variable [MulOneClass M]

/-- On a prime power the product is a single block: `primePowerProd f (p ^ v) = f p v`. The
hypothesis `v ≠ 0` is needed — at `v = 0` the left-hand side is the empty product `1` while the
right-hand side is `f p 0`, and nothing forces those to agree. -/
@[simp]
theorem primePowerProd_prime_pow (f : ℕ → ℕ → M) {p : ℕ} (hp : p.Prime) {v : ℕ} (hv : v ≠ 0) :
    primePowerProd f (p ^ v) = f p v := by
  simpa [hp.pow_minFac hv, hp.factorization_self, Nat.div_self (pow_pos hp.pos v)]
    using primePowerProd_of_one_lt f (Nat.one_lt_pow hv hp.one_lt)

/-- At a prime the product is the single block `f p 1`: the case `v = 1` of
`primePowerProd_prime_pow`, stated separately because a bare prime is not syntactically a
power, so that lemma cannot fire on it. -/
@[simp]
theorem primePowerProd_prime (f : ℕ → ℕ → M) {p : ℕ} (hp : p.Prime) :
    primePowerProd f p = f p 1 := by
  simpa using primePowerProd_prime_pow f hp one_ne_zero

end MulOneClass

section Monoid

variable [Monoid M]

/-- An element commuting with every block of `n` commutes with their ordered product. -/
theorem _root_.Commute.primePowerProd_right (f : ℕ → ℕ → M) {x : M} {n : ℕ}
    (h : ∀ p ∈ n.primeFactors, Commute x (f p (n.factorization p))) :
    Commute x (primePowerProd f n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : 1 < n
    · rw [primePowerProd_of_one_lt f hn]
      refine (h _ (minFac_mem_primeFactors hn)).mul_right (ih _ (ordCompl_minFac_lt hn) ?_)
      intro q hq
      rw [(block_ordCompl hq).2]
      exact h q (block_ordCompl hq).1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (not_lt.1 hn) with rfl | rfl <;> simp

/-- The peeling step for a product `k = m * n` whose least prime `p` does not divide `n`: the
block split off is the block of `m` at `p`, and what remains is the product over
`ordCompl[p] m * n`. Stated with `k` free so that either factor of `m * n` can play `m`. -/
private theorem primePowerProd_of_minFac_not_dvd (f : ℕ → ℕ → M) {k m n p : ℕ} (h1 : 1 < k)
    (hp : k.minFac = p) (hk : k = m * n) (hn : ¬p ∣ n) :
    primePowerProd f k = f p (m.factorization p) * primePowerProd f (ordCompl[p] m * n) := by
  subst hk
  have hm0 : m ≠ 0 := by rintro rfl; simp at h1
  have hn0 : n ≠ 0 := by rintro rfl; simp at h1
  have hblock : (m * n).factorization p = m.factorization p := by
    rw [Nat.factorization_mul hm0 hn0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hn,
      add_zero]
  have hcompl : ordCompl[p] (m * n) = ordCompl[p] m * n := by
    rw [Nat.ordCompl_mul,
      (Nat.ordCompl_eq_self_iff_zero_or_not_dvd n (hp ▸ Nat.minFac_prime h1.ne')).2 (Or.inr hn)]
  rw [primePowerProd_of_one_lt f h1, hp, hcompl, hblock]

/-- The case of `primePowerProd_mul_of_coprime` in which the least prime `p` of `m * n` lies in
`m`, given the induction hypothesis for smaller products: the peeling step splits off the block
of `m` at `p`, the induction hypothesis splits the product over `ordCompl[p] m * n`, and the
peeling step for `m` reassembles `primePowerProd f m`. No commutation is involved. -/
private theorem primePowerProd_mul_of_minFac_dvd_left (f : ℕ → ℕ → M) {m n p : ℕ}
    (hmn : m.Coprime n) (h1 : 1 < m * n) (hp : (m * n).minFac = p) (hpm : p ∣ m)
    (ih : ∀ {m' n' : ℕ}, m' * n' < m * n → m'.Coprime n' →
      (∀ q ∈ m'.primeFactors, ∀ r ∈ n'.primeFactors, r < q →
        Commute (f q (m'.factorization q)) (f r (n'.factorization r))) →
      primePowerProd f (m' * n') = primePowerProd f m' * primePowerProd f n')
    (hf : ∀ q ∈ m.primeFactors, ∀ r ∈ n.primeFactors, r < q →
      Commute (f q (m.factorization q)) (f r (n.factorization r))) :
    primePowerProd f (m * n) = primePowerProd f m * primePowerProd f n := by
  have hrp : p.Prime := hp ▸ Nat.minFac_prime h1.ne'
  have hm0 : m ≠ 0 := by rintro rfl; simp at h1
  have hn0 : n ≠ 0 := by rintro rfl; simp at h1
  have hpn : ¬p ∣ n := hrp.coprime_iff_not_dvd.1 (hmn.coprime_dvd_left hpm)
  have hm1 : 1 < m := hrp.two_le.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hpm)
  have hmin : m.minFac = p :=
    le_antisymm (Nat.minFac_le_of_dvd hrp.two_le hpm)
      (hp ▸ Nat.minFac_le_of_dvd (Nat.minFac_prime hm1.ne').two_le (m.minFac_dvd.mul_right n))
  have hih : primePowerProd f (ordCompl[p] m * n) =
      primePowerProd f (ordCompl[p] m) * primePowerProd f n :=
    ih (Nat.mul_lt_mul_of_pos_right (hmin ▸ ordCompl_minFac_lt hm1) (Nat.pos_of_ne_zero hn0))
      (Nat.Coprime.coprime_dvd_left (Nat.ordCompl_dvd m p) hmn) fun q hq r hr hlt ↦ by
        rw [(block_ordCompl hq).2]; exact hf q (block_ordCompl hq).1 r hr hlt
  calc primePowerProd f (m * n)
      = f p (m.factorization p) * primePowerProd f (ordCompl[p] m * n) :=
        primePowerProd_of_minFac_not_dvd f h1 hp rfl hpn
    _ = f p (m.factorization p) * primePowerProd f (ordCompl[p] m) * primePowerProd f n := by
        rw [hih, mul_assoc]
    _ = primePowerProd f m * primePowerProd f n := by
        rw [← hmin, ← primePowerProd_of_one_lt f hm1]

/-- The case of `primePowerProd_mul_of_coprime` in which the least prime `p` of `m * n` lies in
`n`, given the induction hypothesis for smaller products: the peeling step splits off the block
of `n` at `p` ahead of everything, the induction hypothesis splits the product over
`m * ordCompl[p] n`, and since `p` lies below every prime of `m` the commutation hypothesis
moves that block past `primePowerProd f m`, where the peeling step for `n` reassembles
`primePowerProd f n`. -/
private theorem primePowerProd_mul_of_minFac_dvd_right (f : ℕ → ℕ → M) {m n p : ℕ}
    (hmn : m.Coprime n) (h1 : 1 < m * n) (hp : (m * n).minFac = p) (hpn : p ∣ n)
    (ih : ∀ {m' n' : ℕ}, m' * n' < m * n → m'.Coprime n' →
      (∀ q ∈ m'.primeFactors, ∀ r ∈ n'.primeFactors, r < q →
        Commute (f q (m'.factorization q)) (f r (n'.factorization r))) →
      primePowerProd f (m' * n') = primePowerProd f m' * primePowerProd f n')
    (hf : ∀ q ∈ m.primeFactors, ∀ r ∈ n.primeFactors, r < q →
      Commute (f q (m.factorization q)) (f r (n.factorization r))) :
    primePowerProd f (m * n) = primePowerProd f m * primePowerProd f n := by
  have hrp : p.Prime := hp ▸ Nat.minFac_prime h1.ne'
  have hm0 : m ≠ 0 := by rintro rfl; simp at h1
  have hn0 : n ≠ 0 := by rintro rfl; simp at h1
  have hpm : ¬p ∣ m := hrp.coprime_iff_not_dvd.1 (hmn.symm.coprime_dvd_left hpn)
  have hn1 : 1 < n := hrp.two_le.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn)
  have hmin : n.minFac = p :=
    le_antisymm (Nat.minFac_le_of_dvd hrp.two_le hpn)
      (hp ▸ Nat.minFac_le_of_dvd (Nat.minFac_prime hn1.ne').two_le (n.minFac_dvd.mul_left m))
  have hih : primePowerProd f (m * ordCompl[p] n) =
      primePowerProd f m * primePowerProd f (ordCompl[p] n) :=
    ih (Nat.mul_lt_mul_of_pos_left (hmin ▸ ordCompl_minFac_lt hn1) (Nat.pos_of_ne_zero hm0))
      (hmn.coprime_dvd_right (Nat.ordCompl_dvd n p)) fun q hq r hr hlt ↦ by
        rw [(block_ordCompl hr).2]; exact hf q hq r (block_ordCompl hr).1 hlt
  -- `p` is the least prime of `m * n` and is prime to `m`, so it lies below every prime of `m`
  have hlt : ∀ q ∈ m.primeFactors, p < q := fun q hq ↦ by
    obtain ⟨hq, hqm, -⟩ := Nat.mem_primeFactors.1 hq
    exact lt_of_le_of_ne (hp ▸ Nat.minFac_le_of_dvd hq.two_le (hqm.mul_right n))
      (by rintro rfl; exact hpm hqm)
  have hcomm : Commute (f p (n.factorization p)) (primePowerProd f m) :=
    Commute.primePowerProd_right f fun q hq ↦
      (hf q hq p (Nat.mem_primeFactors.2 ⟨hrp, hpn, hn0⟩) (hlt q hq)).symm
  calc primePowerProd f (m * n)
      = f p (n.factorization p) * primePowerProd f (m * ordCompl[p] n) := by
        rw [primePowerProd_of_minFac_not_dvd f h1 hp (mul_comm m n) hpm,
          mul_comm (ordCompl[p] n) m]
    _ = f p (n.factorization p) * (primePowerProd f m * primePowerProd f (ordCompl[p] n)) := by
        rw [hih]
    _ = primePowerProd f m * (f p (n.factorization p) * primePowerProd f (ordCompl[p] n)) :=
        hcomm.left_comm _
    _ = primePowerProd f m * primePowerProd f n := by
        rw [← hmin, ← primePowerProd_of_one_lt f hn1]

/-- **Multiplicativity on coprime arguments.** When `m` and `n` share no prime, the blocks of
`m * n` are the blocks of `m` together with those of `n`, interleaved by size; sorting them into
the blocks of `m` followed by those of `n` moves each block of `n` past the blocks of `m` at
larger primes, and those are the only pairs asked to commute. In a `CommMonoid` it is discharged
by `fun _ _ _ _ _ ↦ Commute.all _ _`. -/
theorem primePowerProd_mul_of_coprime (f : ℕ → ℕ → M) {m n : ℕ} (hmn : m.Coprime n)
    (hf : ∀ p ∈ m.primeFactors, ∀ q ∈ n.primeFactors, q < p →
      Commute (f p (m.factorization p)) (f q (n.factorization q))) :
    primePowerProd f (m * n) = primePowerProd f m * primePowerProd f n := by
  obtain ⟨k, hk⟩ : ∃ k, m * n = k := ⟨_, rfl⟩
  induction k using Nat.strong_induction_on generalizing m n with
  | _ k ih =>
  subst hk
  by_cases h1 : 1 < m * n
  swap
  · obtain h0 | h0 : m * n = 0 ∨ m * n = 1 := by omega
    · rcases Nat.mul_eq_zero.1 h0 with rfl | rfl
      · simp [(Nat.coprime_zero_left _).1 hmn]
      · simp [(Nat.coprime_zero_right _).1 hmn]
    · obtain ⟨rfl, rfl⟩ : m = 1 ∧ n = 1 :=
        ⟨Nat.eq_one_of_mul_eq_one_right h0, Nat.eq_one_of_mul_eq_one_left h0⟩
      simp
  rcases (Nat.minFac_prime h1.ne').dvd_mul.1 (Nat.minFac_dvd _) with hr | hr
  · exact primePowerProd_mul_of_minFac_dvd_left f hmn h1 rfl hr
      (fun hlt hc hf' ↦ ih _ hlt hc hf' rfl) hf
  · exact primePowerProd_mul_of_minFac_dvd_right f hmn h1 rfl hr
      (fun hlt hc hf' ↦ ih _ hlt hc hf' rfl) hf

end Monoid

section CommMonoid

variable [CommMonoid M]

/-- Once the factors commute the ordering is invisible and the ordered product is the
`Finsupp.prod` over the factorisation. Unconditional in `n`, so it rewrites without a side
goal: at `n = 0` both sides are `1`, the left as the junk value and the right because
`Nat.factorization 0 = 0` has empty support. -/
@[simp]
theorem primePowerProd_eq_factorization_prod (f : ℕ → ℕ → M) (n : ℕ) :
    primePowerProd f n = n.factorization.prod f := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : 1 < n
    · calc primePowerProd f n
          = f n.minFac (n.factorization n.minFac) *
              primePowerProd f (ordCompl[n.minFac] n) := primePowerProd_of_one_lt f h1
        _ = f n.minFac (n.factorization n.minFac) *
              (n.factorization.erase n.minFac).prod f := by
            rw [ih _ (ordCompl_minFac_lt h1), Nat.factorization_ordCompl]
        _ = n.factorization.prod f := Finsupp.mul_prod_erase _ _ _ (minFac_mem_primeFactors h1)
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (not_lt.1 h1) with rfl | rfl <;> simp

end CommMonoid

end Nat

end TauCeti
