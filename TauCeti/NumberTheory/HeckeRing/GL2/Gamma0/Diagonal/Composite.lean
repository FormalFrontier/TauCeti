/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Factorization.PrimePowerProd
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimePower

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

## What is not here

Coprime multiplicativity `T_{mn} = T_m · T_n` and the per-prime product formula both need the
blocks of the `Γ₀(N)` Hecke ring to commute — `TauCeti.Nat.primePowerProd_mul_of_coprime` is
stated in a `Monoid`, but under the hypothesis that each block of `n` commutes with the blocks
of `m` at larger primes, and the Chebyshev manipulation behind the product formula needs a
`CommRing`. That commutativity is not on `main` yet, so neither result is stated here. Nothing
below is blocked by its absence, and `heckeTCompositeGamma0_def` is the hook the multiplicative
half will instantiate through.

## Main definitions

* `HeckeRing.GL2.heckeTCompositeGamma0`: the composite element assembled over the prime
  factorisation of `n`.

## Main results

* `HeckeRing.GL2.heckeTCompositeGamma0_prime_pow`: on a prime power the composite is the
  recurrence family, with no positivity hypothesis.
* `HeckeRing.GL2.heckeTCompositeGamma0_of_one_lt`: the peeling step, as a rewriting rule.
* `HeckeRing.GL2.heckeTCompositeGamma0_prime_pow_of_not_coprime`: at a prime sharing a factor
  with the level the composite degenerates to a power of the generator.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.3 — the multiplicative assembly
  `T_n = ∏_p T_{p^{v_p(n)}}` this file transcribes to the ring.
* Ported from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck,
  `projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/Unified/Gamma0RingDn.lean`,
  declarations `heckeRingDn`, `heckeRingDn_ppow` and `heckeRingDn_peel`. The source guards its
  block map with `if hp : Nat.Prime p then … else 1` because its prime-power family demands a
  primality proof; this file's does not, so the guard is dropped and
  `heckeTCompositeGamma0_prime_pow` loses the source's `0 < v` hypothesis with it. The source's
  peeling combinator `peelProd` is generalised out of the Hecke namespace into
  `TauCeti.Nat.primePowerProd`, where it belongs — it is combinatorics about `Nat.minFac`, with
  no Hecke content.
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

end HeckeRing.GL2
