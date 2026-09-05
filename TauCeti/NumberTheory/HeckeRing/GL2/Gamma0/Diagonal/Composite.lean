/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Factorization.PrimePowerProd.DivisorTable
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.ScalarMul
-- The Atkin–Lehner anti-involution and the commutativity it buys are used only inside proofs,
-- so private: pointwise in `heckeTCompositeGamma0_mul_of_coprime`, and as the structure
-- `commRingHeckeRingGamma0` in `heckeTScalarCompositeGamma0_eq_heckeTScalarGamma0` and
-- `heckeTCompositeGamma0_mul_eq_sum_divisors_gcd`.
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.AtkinLehner

/-!
# The composite diagonal element of the `Γ₀(N)` Hecke ring

`Diagonal/PrimePower.lean` builds the generator `T_p` and the family `T_{p^r}` that the
Diamond–Shurman recurrence produces, and closes by naming its own gap: "the composite element
assembled over a prime factorisation is [not] proved here". This file assembles it.

`heckeTCompositeGamma0 N n` multiplies the blocks `heckeTGeneratorRecGamma0 N p (v_p n)` over
the primes of `n`, least prime first. The assembly is `TauCeti.Nat.primePowerProd` rather than
`n.factorization.prod`: a `Finsupp.prod` needs a `CommMonoid` instance, and the Hecke ring
`𝕋 (Δ₀(N)) (Γ₀(N)) ℤ` carries only a `Ring` one — its commutativity is a theorem about the
Atkin–Lehner anti-involution, not a structure field. The ordered product asks only for `One`
and `Mul` — its bracketing is fixed, so neither associativity nor a unit law enters — and so is
available now.

The block map is `heckeTGeneratorRecGamma0 N` applied directly, with no primality guard. That
is exactly what `Diagonal/PrimePower.lean` bought by dropping `Nat.Prime p` from the recurrence:
the family is total in `p`, so it *is* a block map, and the composite needs no `dite` over
primality and no junk branch to reason around. The primality of `n.minFac` still does all the
mathematical work — it is what `heckeTCompositeGamma0_prime_pow` runs on — but it enters as a
hypothesis of the lemmas rather than as a guard inside the definition.

## What this file adds to the per-prime theory

The *per-prime* product formula is `heckeTGeneratorRecGamma0_mul`, in `Diagonal/PrimePower.lean`,
a statement about the recurrence family with no assembly in it. This file assembles it over a
factorisation, in two forms: multiplicativity at coprime arguments, and the full divisor table at
arbitrary nonzero ones. Both rest on the commutativity of the `Γ₀(N)` Hecke ring, which comes from
the Atkin–Lehner anti-involution.

## Main definitions

* `HeckeRing.GL2.heckeTCompositeGamma0`: the composite element assembled over the prime
  factorisation of `n`.

## Main results

* `HeckeRing.GL2.heckeTCompositeGamma0_prime_pow`: on a prime power the composite is the
  recurrence family, with no positivity hypothesis.
* `HeckeRing.GL2.heckeTCompositeGamma0_of_one_lt`: the peeling step, as a rewriting rule.
* `HeckeRing.GL2.heckeTCompositeGamma0_prime_pow_of_not_coprime`: at a prime sharing a factor
  with the level the composite degenerates to a power of the generator.
* `HeckeRing.GL2.heckeTCompositeGamma0_mul_of_coprime`: the composite is multiplicative on
  coprime arguments, `T_{mn} = T_m · T_n`.
* `HeckeRing.GL2.heckeTCompositeGamma0_mul_eq_sum_divisors_gcd`: **the global multiplication table**
  `T_m · T_n = ∑_{d ∣ gcd m n} d • (S_d · T_{mn/d²})`, for nonzero `m` and `n`. Named after the
  generic theorem it instantiates: `_mul` alone would read as multiplicativity in the index, which
  is the neighbouring `heckeTCompositeGamma0_mul_of_coprime`. At coprime `m` and `n` the gcd is `1`
  and the sum collapses to its `d = 1` term, recovering that lemma.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.3 — the multiplicative assembly
  `T_n = ∏_p T_{p^{v_p(n)}}` this file transcribes to the ring.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3 — Theorem 3.24(3), the multiplication table that
  `heckeTCompositeGamma0_mul_eq_sum_divisors_gcd` states at level `Γ₀(N)`.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck,
  `projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`,
  declarations `heckeRingDn`, `heckeRingDn_ppow`, `heckeRingDn_peel`,
  `heckeRingDn_mul_coprime` and `heckeRingDn_mul` (lines 604-612, the divisor table).
  The source guards its block map with
  `if hp : Nat.Prime p then … else 1` because its prime-power family demands a primality
  proof; this file's does not, so the guard is dropped and
  `heckeTCompositeGamma0_prime_pow` loses the source's `0 < v` hypothesis with it. The source's
  peeling combinator `peelProd` is generalised out of the Hecke namespace into
  `TauCeti.Nat.primePowerProd`, where it belongs — it is combinatorics about `Nat.minFac`, with
  no Hecke content. For coprime multiplicativity the source installs a `CommRing` instance on
  the Hecke ring and calls its `CommMonoid`-level peeling lemma; here
  `TauCeti.Nat.primePowerProd_mul_of_coprime` asks instead for the commutations it actually
  uses, so no instance is swapped in and the obligations are discharged from
  `HeckeCosetModule.mul_comm_of_antiInvolution` directly.
-/

public section

open Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped MatrixGroups HeckeCosetModule

namespace HeckeRing.GL2

variable (N : ℕ) [NeZero N]

/-- The composite element of the `Γ₀(N)` Hecke ring attached to `n`: the product of the
prime-power blocks `heckeTGeneratorRecGamma0 N p (n.factorization p)` over the primes `p ∣ n`,
taken least prime first. At a prime `p` this is the generator `T_p`, at a prime power `p ^ v`
the `v`-th term of the Diamond–Shurman recurrence, and at `1` — as at the junk input `0` — the
identity.

The ordering is an artefact of the weakened typeclass, not of the mathematics: once the Hecke
ring is known to be commutative the factors commute and the product is
`n.factorization.prod (heckeTGeneratorRecGamma0 N)` by
`TauCeti.Nat.primePowerProd_eq_factorization_prod`. -/
noncomputable def heckeTCompositeGamma0 (n : ℕ) : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  TauCeti.Nat.primePowerProd (heckeTGeneratorRecGamma0 N) n

/-- **The defining equation of the composite**: it *is* the ordered product of the recurrence
family over the factorisation. The body is sealed, so without this the
`TauCeti.Nat.primePowerProd` API — in particular the multiplicativity that arrives with
commutativity — is unreachable for it. -/
theorem heckeTCompositeGamma0_def (n : ℕ) :
    heckeTCompositeGamma0 N n = TauCeti.Nat.primePowerProd (heckeTGeneratorRecGamma0 N) n := (rfl)

/-- The junk input: `0` has no factorisation, and the empty product is the identity. -/
@[simp]
theorem heckeTCompositeGamma0_zero : heckeTCompositeGamma0 N 0 = 1 := by
  simpa only [heckeTCompositeGamma0_def] using
    TauCeti.Nat.primePowerProd_zero (heckeTGeneratorRecGamma0 N)

/-- `T₁ = 1`: the empty product over the empty factorisation. -/
@[simp]
theorem heckeTCompositeGamma0_one : heckeTCompositeGamma0 N 1 = 1 := by
  simpa only [heckeTCompositeGamma0_def] using
    TauCeti.Nat.primePowerProd_one (heckeTGeneratorRecGamma0 N)

/-- **The peeling step**: for `1 < n` the composite splits off the block at the least prime
factor of `n`, carrying its whole multiplicity. -/
theorem heckeTCompositeGamma0_of_one_lt {n : ℕ} (hn : 1 < n) : heckeTCompositeGamma0 N n =
    heckeTGeneratorRecGamma0 N n.minFac (n.factorization n.minFac) *
      heckeTCompositeGamma0 N (n / n.minFac ^ n.factorization n.minFac) := by
  simpa only [heckeTCompositeGamma0_def] using
    TauCeti.Nat.primePowerProd_of_one_lt (heckeTGeneratorRecGamma0 N) hn

/-- **On a prime power the composite is the recurrence family**: `T_{p^v}` assembled is
`T_{p^v}` generated.

No positivity is asked of `v`, unlike the general `TauCeti.Nat.primePowerProd_prime_pow`: at
`v = 0` both sides are the identity, the left by `heckeTCompositeGamma0_one` and the right by
`heckeTGeneratorRecGamma0_zero`. That the two junk conventions agree is what lets every
consumer below drop the hypothesis. -/
@[simp]
theorem heckeTCompositeGamma0_prime_pow {p : ℕ} (hp : p.Prime) (v : ℕ) :
    heckeTCompositeGamma0 N (p ^ v) = heckeTGeneratorRecGamma0 N p v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · simpa only [heckeTCompositeGamma0_def] using
      TauCeti.Nat.primePowerProd_prime_pow (heckeTGeneratorRecGamma0 N) hp hv

/-- At a prime the composite is the generator: `T_p` assembled is `T_p`. This is
`TauCeti.Nat.primePowerProd_prime` read through the definition. Marked `@[simp]` alongside
`heckeTCompositeGamma0_prime_pow`, which cannot fire here: a bare prime is not syntactically a
power, so without this lemma a prime input does not reduce to the generator. -/
@[simp]
theorem heckeTCompositeGamma0_prime {p : ℕ} (hp : p.Prime) :
    heckeTCompositeGamma0 N p = heckeTGeneratorGamma0 N p := by
  rw [heckeTCompositeGamma0_def, TauCeti.Nat.primePowerProd_prime _ hp,
    heckeTGeneratorRecGamma0_one]

/-- When `p` shares a factor with the level the scalar term of the recurrence vanishes and the
composite degenerates to a power of the generator: `T_{p^v} = T_p^v`. This is the bad-prime
half of the classical statement, and it is unconditional in `v`. -/
theorem heckeTCompositeGamma0_prime_pow_of_not_coprime {p : ℕ} (hp : p.Prime)
    (hpN : ¬Nat.Coprime p N) (v : ℕ) :
    heckeTCompositeGamma0 N (p ^ v) = heckeTGeneratorGamma0 N p ^ v := by
  rw [heckeTCompositeGamma0_prime_pow N hp v,
    heckeTGeneratorRecGamma0_eq_generator_pow_of_not_coprime N hpN]

/-- **Coprime multiplicativity**: `T_{mn} = T_m · T_n` when `m` and `n` share no prime factor.

The classical multiplicative relation among the `Γ₀(N)` Hecke operators, at the level of the
Hecke ring. Together with `heckeTCompositeGamma0_prime_pow`, which identifies the composite on
a prime power with the Diamond–Shurman recurrence family, it determines `T_n` for every
*positive* `n` from the prime-power data: split `n` into its prime powers here, then evaluate
each factor there. The junk input `0` has no factorisation to split and is fixed separately by
`heckeTCompositeGamma0_zero`. No hypothesis relates `m` or `n` to the level — the bad primes
are already absorbed into the blocks. -/
theorem heckeTCompositeGamma0_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    heckeTCompositeGamma0 N (m * n) = heckeTCompositeGamma0 N m * heckeTCompositeGamma0 N n := by
  -- One application of `primePowerProd_mul_of_coprime`, not an induction: it already sorts the
  -- interleaved blocks of `m * n` into those of `m` followed by those of `n`, and asks back only
  -- that a block of `n` commute with the blocks of `m` at larger primes. The Atkin–Lehner
  -- anti-involution commutes *any* two elements of this ring, so the primes never enter and the
  -- hypothesis is discharged by a constant function. Reading commutativity off that lemma rather
  -- than installing `commSemiringHeckeRingGamma0` as a local instance keeps this statement in the
  -- ambient `Semiring` its neighbours use — the choice `GL2/Recurrence.lean` already makes for
  -- the centrality of the scalar operator.
  simpa only [heckeTCompositeGamma0_def] using
    TauCeti.Nat.primePowerProd_mul_of_coprime (heckeTGeneratorRecGamma0 N) hmn fun _ _ _ _ _ ↦
      HeckeCosetModule.mul_comm_of_antiInvolution ℤ (atkinLehnerAntiInvolution N)
        (atkinLehnerAntiInvolution_onHeckeCoset_eq_self N) _ _

/-! ### The composite scalar, and the global multiplication table -/

/-- The composite **scalar** attached to `n`: the blocks `S_p ^ vₚ(n)` multiplied over the primes
of `n`, least prime first, by the same ordered product that assembles `heckeTCompositeGamma0`.

This is the `S_d` that indexes the divisor sum in
`heckeTCompositeGamma0_mul_eq_sum_divisors_gcd`. At a prime power
it is a power of the scalar operator, at `1` — as at the junk input `0` — the identity. Where `p`
shares a factor with the level `S_p = 0`, so `heckeTScalarCompositeGamma0 N n = 0` as soon as
`n` has such a prime to a positive power. -/
private noncomputable def heckeTScalarCompositeGamma0 (n : ℕ) :
    𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ :=
  TauCeti.Nat.primePowerProd (fun p v ↦ heckeTScalarGamma0 N p ^ v) n

/-- The composite scalar expanded as the ordered product of the blocks `S_p ^ vₚ(n)` over the
primes of `n`. -/
private theorem heckeTScalarCompositeGamma0_def (n : ℕ) :
    heckeTScalarCompositeGamma0 N n =
      TauCeti.Nat.primePowerProd (fun p v ↦ heckeTScalarGamma0 N p ^ v) n := (rfl)

/-- `S₁ = 1`: the empty product over the empty factorisation. -/
@[simp]
private theorem heckeTScalarCompositeGamma0_one : heckeTScalarCompositeGamma0 N 1 = 1 := by
  simpa only [heckeTScalarCompositeGamma0_def] using
    TauCeti.Nat.primePowerProd_one (fun p v ↦ heckeTScalarGamma0 N p ^ v)

/-- **On a prime power the composite scalar is a power of the scalar operator.**

As with `heckeTCompositeGamma0_prime_pow` no positivity is asked of `v`: at `v = 0` both sides
are the identity, the left by `heckeTScalarCompositeGamma0_one` and the right by `pow_zero`. -/
@[simp]
private theorem heckeTScalarCompositeGamma0_prime_pow {p : ℕ} (hp : p.Prime) (v : ℕ) :
    heckeTScalarCompositeGamma0 N (p ^ v) = heckeTScalarGamma0 N p ^ v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · simpa only [heckeTScalarCompositeGamma0_def] using
      TauCeti.Nat.primePowerProd_prime_pow (fun p v ↦ heckeTScalarGamma0 N p ^ v) hp hv

/-- The `Γ₀(N)` Hecke ring over `ℤ` as a *commutative* ring: the ambient `Ring` instance with
`mul_comm` supplied by the Atkin–Lehner anti-involution.

Private and local for the same reason `HeckeRing.GL2.commSemiringHeckeRingGamma0` is not an
instance — the anti-involution is data. -/
@[instance_reducible]
private noncomputable def commRingHeckeRingGamma0 :
    CommRing (𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ) :=
  -- Not `commSemiringHeckeRingGamma0`, which is the same mathematical fact: that one is built from
  -- `instSemiringHeckeRing`, so its `Mul` and `One` are only definitionally the ambient `Ring`'s,
  -- and `rw` through it fails on goals stated with the ambient ones. Extending the ambient `Ring`
  -- keeps the operations syntactically equal.
  { (inferInstance : Ring (𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ)) with
    mul_comm := HeckeCosetModule.mul_comm_of_antiInvolution ℤ (atkinLehnerAntiInvolution N)
      (atkinLehnerAntiInvolution_onHeckeCoset_eq_self N) }

/-- **The assembled scalar is the canonical scalar operator.** At every nonzero index the ordered
product of the blocks `S_p ^ vₚ(n)` is `S_n` itself, so the divisor table below is stated with the
scalar family the rest of the level-`N` Hecke API uses, and the assembled one never reaches a
consumer.

`0` is excluded because the two disagree there: the empty product is the identity, while
`S₀ = 0`. -/
private theorem heckeTScalarCompositeGamma0_eq_heckeTScalarGamma0 :
    ∀ {n : ℕ}, n ≠ 0 → heckeTScalarCompositeGamma0 N n = heckeTScalarGamma0 N n := by
  let := commRingHeckeRingGamma0 N
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn) with h1 | h1
    · simp [← h1]
    · have hp : (n.minFac).Prime := Nat.minFac_prime (by omega)
      have hv : n.factorization n.minFac ≠ 0 :=
        (hp.factorization_pos_of_dvd hn (Nat.minFac_dvd n)).ne'
      have hlt : ordCompl[n.minFac] n < n :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hn) (Nat.one_lt_pow hv hp.one_lt)
      have hne : ordCompl[n.minFac] n ≠ 0 := (Nat.ordCompl_pos n.minFac hn).ne'
      rw [heckeTScalarCompositeGamma0_def,
        TauCeti.Nat.primePowerProd_eq_ordProj_mul_ordCompl
          (fun q w ↦ heckeTScalarGamma0 N q ^ w) hp hn,
        ← heckeTScalarCompositeGamma0_def, ← heckeTScalarCompositeGamma0_def,
        heckeTScalarCompositeGamma0_prime_pow N hp, ih _ hlt hne, heckeTScalarGamma0_pow,
        heckeTScalarGamma0_mul, Nat.ordProj_mul_ordCompl_eq_self]

/-- **Shimura, Theorem 3.24(3)** at level `Γ₀(N)`, in full — the global multiplication table:

`T_m · T_n = ∑_{d ∣ gcd m n} d • (S_d · T_{mn/d²})`.

This is the composite counterpart of `heckeTGeneratorRecGamma0_mul`, which is the same identity
one prime at a time. At coprime `m` and `n` it specialises to
`heckeTCompositeGamma0_mul_of_coprime`: the gcd is `1`, the sum collapses to its `d = 1` term, and
`S₁ = 1` leaves `T_m · T_n`.

Both arguments must be nonzero. `heckeTCompositeGamma0` sends `0` to the empty product `1` and
`gcd 0 0 = 0` has no divisors, so at `m = n = 0` the left side is `1` and the right an empty sum.

Together with `heckeTCompositeGamma0_prime_pow` this determines every product of two composite
elements from the prime-power data. Divisors sharing a factor with the level contribute nothing,
by `heckeTScalarGamma0_of_not_coprime`, so the sum over *all* divisors of
`gcd m n` is the right index even though only the good ones carry weight. -/
theorem heckeTCompositeGamma0_mul_eq_sum_divisors_gcd {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    heckeTCompositeGamma0 N m * heckeTCompositeGamma0 N n =
      ∑ d ∈ (Nat.gcd m n).divisors, (d : ℤ) •
        (heckeTScalarGamma0 N d * heckeTCompositeGamma0 N (m * n / d ^ 2)) := by
  let := commRingHeckeRingGamma0 N
  rw [Finset.sum_congr rfl fun d hd ↦ congrArg _ (congrArg (· * _)
    (heckeTScalarCompositeGamma0_eq_heckeTScalarGamma0 N
      (Nat.pos_of_mem_divisors hd).ne').symm)]
  -- The generic table is stated over a `CommSemiring` with `ℕ`-scalars; the Hecke ring is a
  -- `Ring`, where `natCast_zsmul` identifies those with the `ℤ`-scalars its neighbours use.
  simp only [heckeTCompositeGamma0_def, heckeTScalarCompositeGamma0_def,
    show ∀ (d : ℕ) (x : 𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ), (d : ℤ) • x = d • x from
      fun d x ↦ natCast_zsmul x d]
  refine TauCeti.Nat.primePowerProd_mul_eq_sum_divisors_gcd _ _ (fun p hp r s hrs ↦ ?_) hm hn
  -- The per-prime table is `heckeTGeneratorRecGamma0_mul`; all that is needed is to read the
  -- assembled products at prime powers back as the blocks they are assembled from.
  have hD : ∀ v : ℕ, TauCeti.Nat.primePowerProd (heckeTGeneratorRecGamma0 N) (p ^ v) =
      heckeTGeneratorRecGamma0 N p v := fun v ↦
    (heckeTCompositeGamma0_def N (p ^ v)).symm.trans (heckeTCompositeGamma0_prime_pow N hp v)
  have hS : ∀ v : ℕ,
      TauCeti.Nat.primePowerProd (fun q w ↦ heckeTScalarGamma0 N q ^ w) (p ^ v) =
        heckeTScalarGamma0 N p ^ v := fun v ↦
    (heckeTScalarCompositeGamma0_def N (p ^ v)).symm.trans
      (heckeTScalarCompositeGamma0_prime_pow N hp v)
  simp only [hD, hS]
  refine (heckeTGeneratorRecGamma0_mul N p hrs).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  exact natCast_zsmul _ _

end HeckeRing.GL2
