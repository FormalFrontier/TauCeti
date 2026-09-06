/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
public import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
public import TauCeti.NumberTheory.NumberField.ArtinSymbol

/-!
# The ideal weight of a Galois character

For a finite Galois extension `L / K` of number fields and a character `χ : Gal(L/K) →* ℂˣ`, this
file builds the *canonical ideal weight* `galoisCharacterWeight χ`: the completely multiplicative
function on the ideals of `𝓞 K` whose value at a height-one prime `𝔭` is `χ (Frob 𝔭)` when `𝔭` is
unramified in `L`, and `0` when `𝔭` ramifies.

Nothing here assumes that `L / K` is cyclotomic: the construction needs only `[IsGalois K L]`, and
the character is an arbitrary degree-one complex character of the Galois group. The Dirichlet
weight is the specialisation `L / K = ℚ(ζ_m) / ℚ`, where the cyclotomic character identifies
`Gal(ℚ(ζ_m)/ℚ)` with `(ZMod m)ˣ` and `χ` is a Dirichlet character mod `m`. Over a general base `K`
that character is still injective but need not be surjective: restriction identifies
`Gal(K(ζ_m)/K)` with the subgroup of `(ZMod m)ˣ` fixing `K ∩ ℚ(ζ_m)`, and that subgroup is all of
`(ZMod m)ˣ` exactly when `K ∩ ℚ(ζ_m) = ℚ`. The declarations are named for the generality they
actually have.

The weight is **total**, and that is a design constraint rather than a convenience: a weight
specified only away from ramification leaves its values at the bad primes unconstrained, so the
Euler product and the orthogonality identities would not pin it down. Vanishing at the ramified
primes is what makes the ramified Euler factors drop out as `(1 - 0)⁻¹ = 1`.

## Main definitions

* `MonoidHom.galoisCharacterWeight`: the weight of `χ`, packaged as a
  `TauCeti.MultiplicativeIdealWeight K`.

## Main results

* `MonoidHom.galoisCharacterWeight_apply_of_unramified`: at an unramified height-one prime the
  weight is `χ` of the Artin symbol.
* `MonoidHom.galoisCharacterWeight_apply_eq_zero_iff`: the weight vanishes at a height-one prime
  exactly when that prime ramifies in `L`.
* `MonoidHom.badPrimes_galoisCharacterWeight`: the bad primes of the weight are exactly the
  ramified primes.

## Implementation notes

The weight is packaged as a `TauCeti.MultiplicativeIdealWeight K` rather than as a bare function
`Ideal (𝓞 K) → ℂ`, so that the totality above is expressed in the carrier's own `badPrimes` API:
the bad primes of `χ.galoisCharacterWeight` are exactly `ramifiedPrimes K L`.

## References

Adapted from `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_mul` and
`norm_galoisCharacterOnIdeal_le_one` in `CebotarevDensity/ZetaProduct.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, following Sharifi,
*Algebraic Number Theory*, Notation 7.1.17. The factorization-product definition and the
`Multiset.map_add`/`Multiset.prod_add` multiplicativity argument are the source's; the
`MultiplicativeIdealWeight` packaging and the `artinSymbol` totalization are not the source's and
are new here. The source likewise names the construction for a general Galois character.
-/

public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

open UniqueFactorizationMonoid

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open scoped Classical in
/-- The value of `galoisCharacterWeight χ` at a single prime: `χ (Frob 𝔭)` at an unramified
maximal `𝔭`, and `0` otherwise. -/
private noncomputable def galoisCharacterPrimeValue (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔭 : Ideal (𝓞 K)) :
    ℂ :=
  -- The unramifiedness clause is spelled out rather than named because it is, character for
  -- character, `artinSymbol`'s `hur` hypothesis: `h.2` is handed to it directly below.
  if h : 𝔭.IsMaximal ∧ ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q then
    have : 𝔭.IsMaximal := h.1
    (χ (artinSymbol (L := L) 𝔭 h.2).out : ℂ)
  else 0

open scoped Classical in
/-- The prime value extended to all ideals completely multiplicatively through the prime
factorization, with the zero ideal sent to `0`. -/
private noncomputable def galoisCharacterWeightFun (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 : Ideal (𝓞 K)) :
    ℂ :=
  if 𝔞 = ⊥ then 0
  else ((normalizedFactors 𝔞).map (galoisCharacterPrimeValue (L := L) χ)).prod

/-- The zero ideal has weight `0`. -/
private theorem galoisCharacterWeightFun_bot (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    galoisCharacterWeightFun (L := L) χ ⊥ = 0 := by
  simp [galoisCharacterWeightFun]

/-- Away from the zero ideal the weight is the factorization product. -/
private theorem galoisCharacterWeightFun_of_ne_bot (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔞 : Ideal (𝓞 K)}
    (h𝔞 : 𝔞 ≠ ⊥) :
    galoisCharacterWeightFun (L := L) χ 𝔞 =
      ((normalizedFactors 𝔞).map (galoisCharacterPrimeValue (L := L) χ)).prod := by
  simp [galoisCharacterWeightFun, h𝔞]

/-- The unit ideal has weight `1`. -/
private theorem galoisCharacterWeightFun_top (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    galoisCharacterWeightFun (L := L) χ ⊤ = 1 := by
  rw [galoisCharacterWeightFun_of_ne_bot χ top_ne_bot, ← Ideal.one_eq_top,
    normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]

/-- **Complete multiplicativity.** The weight of a product of ideals is the product of the
weights. -/
private theorem galoisCharacterWeightFun_mul (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 𝔟 : Ideal (𝓞 K)) :
    galoisCharacterWeightFun (L := L) χ (𝔞 * 𝔟) =
      galoisCharacterWeightFun (L := L) χ 𝔞 * galoisCharacterWeightFun (L := L) χ 𝔟 := by
  -- Both degenerate cases collapse: `⊥ * 𝔟 = ⊥` and `𝔞 * ⊥ = ⊥`, so each side is `0`.
  rcases eq_or_ne 𝔞 ⊥ with rfl | h𝔞
  · simp [galoisCharacterWeightFun_bot]
  rcases eq_or_ne 𝔟 ⊥ with rfl | h𝔟
  · simp [galoisCharacterWeightFun_bot]
  -- `Ideal.mul_eq_bot`, not `mul_ne_zero`: the latter produces `𝔞 * 𝔟 ≠ 0`, and although `0` and
  -- `⊥` are definitionally equal for ideals they are not syntactically equal, so `rw` cannot
  -- match it against the `⊥` in the definition.
  have hab : 𝔞 * 𝔟 ≠ ⊥ := fun h ↦ (Ideal.mul_eq_bot.mp h).elim h𝔞 h𝔟
  rw [galoisCharacterWeightFun_of_ne_bot χ hab, galoisCharacterWeightFun_of_ne_bot χ h𝔞,
    galoisCharacterWeightFun_of_ne_bot χ h𝔟, normalizedFactors_mul h𝔞 h𝔟,
    Multiset.map_add, Multiset.prod_add]

/-- On a height-one prime the weight is just the single prime value. -/
private theorem galoisCharacterWeightFun_heightOne (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    galoisCharacterWeightFun (L := L) χ 𝔭.asIdeal =
      galoisCharacterPrimeValue (L := L) χ 𝔭.asIdeal := by
  -- The factorization of a prime ideal is the one-element multiset.
  simp only [galoisCharacterWeightFun_of_ne_bot χ 𝔭.ne_bot,
    normalizedFactors_irreducible 𝔭.irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

/-- The weight vanishes at a height-one prime exactly when that prime ramifies in `L`. -/
private theorem galoisCharacterWeightFun_heightOne_eq_zero_iff (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    galoisCharacterWeightFun (L := L) χ 𝔭.asIdeal = 0 ↔ 𝔭 ∈ ramifiedPrimes K L := by
  rw [galoisCharacterWeightFun_heightOne, galoisCharacterPrimeValue, mem_ramifiedPrimes_iff]
  -- A height-one prime is maximal, so the `dite` condition reduces to unramifiedness.
  split_ifs with h
  · exact iff_of_false (Units.ne_zero _) (not_not_intro h.2)
  · exact iff_of_true rfl fun hc ↦ h ⟨𝔭.isMaximal, hc⟩

end NumberField.Chebotarev

open NumberField NumberField.Chebotarev

namespace MonoidHom

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **The ideal weight of a Galois character** `χ`, packaged as a `MultiplicativeIdealWeight`. On a
height-one prime it is `χ (Frob 𝔭)` at the unramified primes and `0` at the ramified ones, extended
to all ideals completely multiplicatively through the prime factorization. -/
noncomputable def galoisCharacterWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    TauCeti.MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    { toFun := galoisCharacterWeightFun (L := L) χ
      map_zero' := galoisCharacterWeightFun_bot χ
      map_one' := by simpa using galoisCharacterWeightFun_top (L := L) χ
      map_mul' := galoisCharacterWeightFun_mul χ }
  -- The vanishing set is exactly `ramifiedPrimes K L`, which is already a `Finset`.
  finite_setOf_apply_eq_zero := (ramifiedPrimes K L).finite_toSet.subset fun 𝔭 h𝔭 ↦
    (galoisCharacterWeightFun_heightOne_eq_zero_iff χ 𝔭).mp h𝔭

/-- Defining equation of `galoisCharacterWeight`; its body is not exposed. -/
private theorem galoisCharacterWeight_apply (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 : Ideal (𝓞 K)) :
    galoisCharacterWeight (L := L) χ 𝔞 = galoisCharacterWeightFun (L := L) χ 𝔞 := (rfl)

/-- **Value at an unramified prime.** At a height-one prime unramified in `L` the weight is `χ` of
the Artin symbol; together with the vanishing at ramified primes and complete multiplicativity this
determines the weight. -/
theorem galoisCharacterWeight_apply_of_unramified (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K))
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
    galoisCharacterWeight (L := L) χ 𝔭.asIdeal =
      (χ (artinSymbol (L := L) 𝔭.asIdeal hur).out : ℂ) := by
  rw [galoisCharacterWeight_apply, galoisCharacterWeightFun_heightOne, galoisCharacterPrimeValue]
  -- The `dite` condition holds: a height-one prime is maximal, and `hur` is its second half.
  -- Both branches close by proof irrelevance in the unramifiedness and maximality proofs.
  split_ifs with h
  · rfl
  · exact absurd ⟨𝔭.isMaximal, hur⟩ h

/-- The weight vanishes at a height-one prime exactly when that prime ramifies in `L`. This is what
makes the weight *total*: the bad primes are not left unconstrained, they are pinned to `0`. -/
@[simp]
theorem galoisCharacterWeight_apply_eq_zero_iff (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    galoisCharacterWeight (L := L) χ 𝔭.asIdeal = 0 ↔ 𝔭 ∈ ramifiedPrimes K L := by
  rw [galoisCharacterWeight_apply]
  exact galoisCharacterWeightFun_heightOne_eq_zero_iff χ 𝔭

/-- The bad primes of the weight are exactly the ramified primes. -/
@[simp]
theorem badPrimes_galoisCharacterWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    (galoisCharacterWeight (L := L) χ).badPrimes = ↑(ramifiedPrimes K L) := by
  ext 𝔭
  simpa only [TauCeti.MultiplicativeIdealWeight.mem_badPrimes, Finset.mem_coe] using
    galoisCharacterWeight_apply_eq_zero_iff χ 𝔭

end MonoidHom
