/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Abelian
public import TauCeti.NumberTheory.NumberField.ArtinSymbol
public import TauCeti.NumberTheory.NumberField.Ideal.Away
import Mathlib.Algebra.Group.IsCommutative
import TauCeti.Algebra.Group.Conj

/-!
# The ideal-theoretic Artin map away from a finite set of primes

Let `L/K` be a finite abelian extension of number fields and let `S` be a finite set of finite
places of `K` outside which `L/K` is unramified. At a prime `v ∉ S` the Artin symbol is a
conjugacy class in an abelian group, hence a single automorphism, and extending that assignment
multiplicatively over the unique factorization of fractional ideals gives the **Artin map**

`artinHomAway : idealsAway S →* (L ≃ₐ[K] L)`

on the group `idealsAway S` of invertible fractional ideals of multiplicity zero along `S`.

The excluded set `S` is a parameter: no relation between `S` and the ramified primes is assumed
beyond the hypothesis `hur` that every prime outside `S` is unramified. Specializing `S` to the
support of the relative discriminant, or to the support of a modulus, is a separate matter.

Commutativity of `Gal(L/K)` enters as an explicit hypothesis `hab` rather than as an instance,
because the ambient group is a Galois group of a general extension. Where the construction needs
a bundled commutative structure — for the bijection between the group and its conjugacy classes,
and for the finitely supported product over all primes — the scoped `Group` plus
`IsMulCommutative` instance supplies it.

Nothing about the kernel, the image, or a factorization through ray class groups is proved here.

The construction follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter VI, §7.

## Main definitions

* `TauCeti.NumberFieldArithmetic.artinElementAway`: the Artin automorphism at a prime outside `S`,
  extended by `1` on `S`.
* `TauCeti.NumberFieldArithmetic.artinHomAway`: the Artin map on `idealsAway S`.
* `TauCeti.NumberFieldArithmetic.artinHomAwayIntegral`: its restriction to the integral ideals
  prime to `S`.

## Main results

* `TauCeti.NumberFieldArithmetic.artinHomAway_apply`: the value at an ideal is the product of the
  local Artin automorphisms with the multiplicities of the ideal as exponents.
* `TauCeti.NumberFieldArithmetic.artinHomAway_apply_prime`: the value at a prime outside `S` is
  the Frobenius there.
* `TauCeti.NumberFieldArithmetic.artinHomAway_eq_of_apply_prime`: those values determine the map.
* `TauCeti.NumberFieldArithmetic.artinHomAway_mono`: enlarging `S` restricts the map.
* `TauCeti.NumberFieldArithmetic.artinHomAway_restrict`: restriction of automorphisms to an
  intermediate field carries the Artin map of `L/K` to the Artin map of `M/K`.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField IsMulCommutative

namespace TauCeti.NumberFieldArithmetic

variable {K : Type*} [Field K] [NumberField K]

section ArtinHomAway

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)

open scoped Classical in
/-- The Artin automorphism at a finite place of `K`, extended by `1` inside the excluded set `S`.

At `v ∉ S` this is the unique element of the Artin symbol of `v`, taken through the bijection
`ConjClasses.mkEquiv` between an abelian group and its conjugacy classes. The commutativity
hypothesis `hab` is what makes that bijection available, so without it there is no automorphism
here to name and only the class `artinSymbol` is defined. -/
noncomputable def artinElementAway (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)
    (v : HeightOneSpectrum (𝓞 K)) : L ≃ₐ[K] L :=
  letI : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨fun σ τ ↦ (hab σ τ).eq⟩⟩
  if hv : v ∈ S then 1 else ConjClasses.mkEquiv.symm (artinSymbol (L := L) v.asIdeal (hur v hv))

/-- Inside the excluded set the Artin automorphism is trivial by definition. -/
@[simp]
theorem artinElementAway_eq_one_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    artinElementAway (L := L) hab S hur v = 1 :=
  dite_eq_left hv

/-- Outside the excluded set the Artin automorphism represents the Artin symbol. -/
theorem artinSymbol_eq_mk_artinElementAway {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    artinSymbol (L := L) v.asIdeal (hur v hv) =
      ConjClasses.mk (artinElementAway hab S hur v) := by
  have : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨fun σ τ ↦ (hab σ τ).eq⟩⟩
  rw [artinElementAway, dite_eq_right hv]
  exact (ConjClasses.mkEquiv.apply_symm_apply _).symm

include hab in
/-- **The Artin automorphism at `v ∉ S` is an arithmetic Frobenius at every prime above `v`.**
For a general Galois extension only the conjugacy class of a Frobenius is attached to `v`; here
the class is a single element, so it is a Frobenius at each prime above `v` at once. -/
theorem isArithFrobAt_artinElementAway {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] :
    IsArithFrobAt (𝓞 K) (artinElementAway hab S hur v) Q := by
  have : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨fun σ τ ↦ (hab σ τ).eq⟩⟩
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  have hconj : IsConj (artinElementAway hab S hur v) σ :=
    ConjClasses.mk_eq_mk_iff_isConj.mp <|
      (artinSymbol_eq_mk_artinElementAway hab S hur hv).symm.trans
        (artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal (hur v hv) Q σ hσ)
  exact isConj_iff_eq.mp hconj ▸ hσ

include hab in
/-- **The Artin automorphism at `v ∉ S` is the Frobenius there.** Any arithmetic Frobenius at any
prime above `v` equals it, which is what makes the assignment `v ↦ artinElementAway hab S hur v`
well defined without a choice of prime above `v`. -/
theorem artinElementAway_eq_of_isArithFrobAt {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    artinElementAway hab S hur v = σ := by
  have : Algebra.IsUnramifiedAt (𝓞 K) Q := hur v hv Q
  exact isArithFrobAt_eq_of_isUnramifiedAt (isArithFrobAt_artinElementAway hab S hur hv Q) hσ

/-- **The ideal-theoretic Artin map.** The multiplicative extension of `artinElementAway` along
the unique factorization of an invertible fractional ideal, on the group of fractional ideals
with multiplicity zero at every prime of `S`. -/
noncomputable def artinHomAway : idealsAway (K := K) S →* (L ≃ₐ[K] L) :=
  letI : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨fun σ τ ↦ (hab σ τ).eq⟩⟩
  MonoidHom.mk' (fun I ↦ ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinElementAway hab S hur v ^
      FractionalIdeal.count K v ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
    fun I J ↦ by
      refine Eq.trans (finprod_congr fun v ↦ ?_)
        (finprod_mul_distrib (FractionalIdeal.hasFiniteMulSupport_zpow_count _ _)
          (FractionalIdeal.hasFiniteMulSupport_zpow_count _ _))
      rw [Subgroup.coe_mul, Units.val_mul,
        FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _), zpow_add]

/-- **The Artin map is the product of the local Artin automorphisms, with the multiplicities of
the ideal as exponents.** The product is over all finite places of `K`, all but finitely many
factors being trivial. It is taken in the commutative structure that `hab` itself supplies, so
no bundled commutativity is asked of the caller. -/
theorem artinHomAway_apply (I : idealsAway (K := K) S) :
    artinHomAway (L := L) hab S hur I =
      letI : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨fun σ τ ↦ (hab σ τ).eq⟩⟩
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinElementAway hab S hur v ^ FractionalIdeal.count K v
        ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := (rfl)

/-- **The value of the Artin map at a prime outside `S` is the Frobenius there.** -/
theorem artinHomAway_apply_prime (I : idealsAway (K := K) S) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S)
    (hI : ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K))
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] (σ : L ≃ₐ[K] L)
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    artinHomAway (L := L) hab S hur I = σ := by
  have : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨fun a b ↦ (hab a b).eq⟩⟩
  -- Only the factor at `v` survives the product of `artinHomAway_apply`.
  rw [artinHomAway_apply hab S hur I, finprod_eq_single _ v, hI, FractionalIdeal.count_self,
    zpow_one, artinElementAway_eq_of_isArithFrobAt hab S hur hv Q hσ]
  intro w hw
  rw [hI, FractionalIdeal.count_maximal_coprime K w (Ne.symm hw), zpow_zero]

/-- **The values on the primes outside `S` determine the Artin map.** The carrier is generated by
those primes, so a homomorphism taking the Frobenius value at each of them is the Artin map. -/
theorem artinHomAway_eq_of_apply_prime (φ : idealsAway (K := K) S →* (L ≃ₐ[K] L))
    (hφ : ∀ (I : idealsAway (K := K) S) (v : HeightOneSpectrum (𝓞 K)), v ∉ S →
      ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) →
      ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver v.asIdeal) (σ : L ≃ₐ[K] L),
        IsArithFrobAt (𝓞 K) σ Q → φ I = σ) :
    φ = artinHomAway (L := L) hab S hur := by
  -- Every generator of the carrier lies in the image of the equalizer of the two homomorphisms,
  -- and the carrier is generated by the primes outside `S`.
  have key : ∀ J ∈ idealsAway (K := K) S, J ∈ Subgroup.map (idealsAway (K := K) S).subtype
      (φ.eqLocus (artinHomAway hab S hur)) := by
    intro J₀ hJ₀
    rw [idealsAway_eq_closure_primes] at hJ₀
    refine (Subgroup.closure_le _).mpr ?_ hJ₀
    rintro J ⟨v, hv, hJ⟩
    have hmem : J ∈ idealsAway (K := K) S := by
      refine mem_idealsAway_iff.mpr fun w hw ↦ ?_
      have hwv : w ≠ v := fun hwv ↦ hv (hwv ▸ hw)
      rw [hJ, FractionalIdeal.count_maximal_coprime K w (Ne.symm hwv)]
    obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
    obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
    have heq : φ ⟨J, hmem⟩ = artinHomAway (L := L) hab S hur ⟨J, hmem⟩ := by
      rw [hφ ⟨J, hmem⟩ v hv hJ Q ‹_› ‹_› σ hσ,
        artinHomAway_apply_prime hab S hur ⟨J, hmem⟩ v hv hJ Q σ hσ]
    exact ⟨⟨J, hmem⟩, heq, rfl⟩
  refine MonoidHom.ext fun I ↦ ?_
  obtain ⟨y, hy, hyI⟩ := key I I.2
  exact (Subtype.ext hyI : y = I) ▸ hy

/-- **Enlarging the excluded set restricts the Artin map.** For `S ⊆ S'` the Artin map for `S'`
is the Artin map for `S` composed with the inclusion of carriers. -/
theorem artinHomAway_mono (S' : Finset (HeightOneSpectrum (𝓞 K))) (h : S ⊆ S')
    (hur' : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
      ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q) :
    artinHomAway (L := L) hab S' hur' =
      (artinHomAway (L := L) hab S hur).comp (idealsAwayInclusion h) := by
  refine (artinHomAway_eq_of_apply_prime hab S' hur' _ ?_).symm
  intro I v hv hI Q hQp hQl σ hσ
  exact artinHomAway_apply_prime hab S hur (idealsAwayInclusion h I) v (fun hvS ↦ hv (h hvS))
    (by rw [coe_idealsAwayInclusion]; exact hI) Q σ hσ

end ArtinHomAway

section Restrict

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)

/-- **The Artin map is functorial in the top field.** Restriction of automorphisms to a normal
intermediate field `M` carries the Artin map of `L/K` to the Artin map of `M/K`, over the same
excluded set and with both the commutativity and the unramifiedness hypothesis for `M/K` derived
from the ones for `L/K`. -/
theorem artinHomAway_restrict (M : IntermediateField K L) [IsGalois K M] :
    (AlgEquiv.restrictNormalHom (F := K) M).comp (artinHomAway (L := L) hab S hur) =
      artinHomAway (L := M) (commute_of_intermediateField hab M) S
        (isUnramifiedAway_of_intermediateField M S hur) := by
  refine artinHomAway_eq_of_apply_prime (commute_of_intermediateField hab M) S _ _ ?_
  intro I v hv hI P hPp hPl τ hτ
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  have : IsMulCommutative (M ≃ₐ[K] M) :=
    ⟨⟨fun a b ↦ (commute_of_intermediateField hab M a b).eq⟩⟩
  rw [MonoidHom.comp_apply, artinHomAway_apply_prime hab S hur I v hv hI Q σ hσ]
  -- Both sides represent the Artin symbol of `v` for `M/K`, which is the image of the one for
  -- `L/K` under restriction; in a commutative group a class has only one representative.
  refine ConjClasses.mk_injective ?_
  rw [← ConjClasses.map_mk (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M) σ,
    ← artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal (hur v hv) Q σ hσ,
    artinSymbol_map_restrictNormalHom v.asIdeal (hur v hv),
    artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal _ P τ hτ]

end Restrict

section Integral

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)

/-- **The integral Artin homomorphism.** The Artin map read on the monoid of nonzero integral
ideals divisible by no prime of `S`; this is the shape the classical statements take. -/
noncomputable def artinHomAwayIntegral : integralIdealsAway (K := K) S →* (L ≃ₐ[K] L) :=
  (artinHomAway (L := L) hab S hur).comp (integralIdealsAwayHom S)

/-- **The integral Artin homomorphism is the Artin map read through the inclusion of the integral
ideals prime to `S` into `idealsAway S`.** -/
@[simp]
theorem artinHomAwayIntegral_apply (I : integralIdealsAway (K := K) S) :
    artinHomAwayIntegral (L := L) hab S hur I =
      artinHomAway (L := L) hab S hur (integralIdealsAwayHom S I) :=
  (rfl)

/-- **The value of the integral Artin homomorphism at a prime outside `S` is the Frobenius
there.** -/
theorem artinHomAwayIntegral_apply_prime (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (hmem : v.asIdeal ∈ integralIdealsAway (K := K) S)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] (σ : L ≃ₐ[K] L)
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    artinHomAwayIntegral (L := L) hab S hur ⟨v.asIdeal, hmem⟩ = σ :=
  artinHomAway_apply_prime hab S hur _ v hv
    (coe_integralIdealsAwayHom S ⟨v.asIdeal, hmem⟩) Q σ hσ

end Integral

end TauCeti.NumberFieldArithmetic
