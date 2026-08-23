/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Integral
public import TauCeti.FieldTheory.FunctionField.Place.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation

/-!
# Affine models: a place finite on a Dedekind subring is one of its height one primes

An *affine model* of `F / k` is a Dedekind `k`-subalgebra `R` of `F` whose fraction field is `F`;
the standard example is the integral closure `R_x` of `k[x]` in `F` for a transcendental `x`. This
file proves the forward direction of the places ↔ height one primes correspondence: a place of
`F / k` whose valuation ring contains `R` is the adic place of a *unique* height one prime `𝔭` of
`R`, in the strong sense that the valuation of the place *equals* — not merely is equivalent to —
the normalized `𝔭`-adic valuation. The prime in question is the centre `{r : R | ord_P r > 0}` of
the place on `R`, so the valuation ring of the place is the localization of `R` there. The converse
— that every height one prime of `R` arises this way, which upgrades this injection into a
bijection — is not proved here; it is proved in
`TauCeti/FieldTheory/FunctionField/AffineModel/Prime.lean`, which constructs the place of a
prime.

This is the "places → height one primes" half of the affine-model dictionary that reduces divisor
theory on the finite chart of a model to Mathlib's factorization calculus for fractional ideals.
Which places are finite on `R_x` is settled by the two order-of-`x` criteria below: `k[x]` lies in
the valuation ring of `P` exactly when `x` has no pole at `P`, and the valuation ring, being
integrally closed, then swallows everything integral over `k[x]`.

## Main results

* `TauCeti.Place.mem_integers_of_isIntegral`: the valuation ring of a place is integrally closed,
  so it contains everything integral over a subring it contains.
* `TauCeti.Place.adjoin_le_integers_iff`: `k[x] ⊆ 𝒪_P` exactly when `x ∈ 𝒪_P`.
* `TauCeti.Place.center`: the height one prime of an affine model below a place finite on it,
  with `TauCeti.Place.valuation_center` identifying the adic valuation of that prime with the
  valuation of the place, and `TauCeti.Place.center_injective` showing that a place finite on a
  model is determined by its centre.
* `TauCeti.Place.existsUnique_valuation_eq`: the uniqueness statement, and
  `TauCeti.Place.valuationSubringAtPrime_eq_integers`: the valuation ring of the place is the
  localization of the model at the centre.
* `TauCeti.Place.ord_algebraMap_eq_multiplicity_center`: the coefficient formula
  `ord_P r = mult_(centre) (r)`, which reads an order at the place off the factorization of an
  ideal of the model.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.1 and III.2.
-/

public section

open IsDedekindDomain

namespace TauCeti

namespace Place

universe u v w

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F] (P : Place k F)

section Integers

/-- The valuation ring of a place is integrally closed in `F`: an element of `F` integral over a
`k`-algebra whose image lies in `𝒪_P` lies in `𝒪_P`. -/
theorem mem_integers_of_isIntegral {R : Type w} [CommRing R] [Algebra R F]
    (hR : ∀ r : R, algebraMap R F r ∈ P.integers) {y : F} (hy : IsIntegral R y) :
    y ∈ P.integers := by
  have hR' : ∀ r : R, algebraMap R F r ∈ P.valuation.valuationSubring :=
    fun r ↦ P.mem_integers_iff.mp (hR r)
  let : Algebra R P.valuation.valuationSubring := ((algebraMap R F).codRestrict _ hR').toAlgebra
  have : IsScalarTower R P.valuation.valuationSubring F := .of_algebraMap_eq fun _ ↦ rfl
  exact P.mem_integers_iff.mpr
    ((Valuation.valuationSubring.integers P.valuation).isIntegral_iff_v_le_one.mp hy.tower_top)

/-- **`k[x]` lies in the valuation ring of `P` exactly when `x` has no pole at `P`**: the
criterion selecting the places on the finite chart of `x`. Its additive form is obtained from
`TauCeti.Place.mem_integers_iff_ord_nonneg`. -/
theorem adjoin_le_integers_iff {x : F} :
    (∀ y ∈ Algebra.adjoin k ({x} : Set F), y ∈ P.integers) ↔ x ∈ P.integers :=
  ⟨fun h ↦ h x (Algebra.self_mem_adjoin_singleton k x), fun hx _ hy ↦
    Algebra.adjoin_le (S := Subalgebra.mk P.integers.toSubring.toSubsemiring
      P.algebraMap_mem_integers) (Set.singleton_subset_iff.mpr (by simpa using hx)) hy⟩

/-- Every element of `F` integral over `k[x]` lies in the valuation ring of `P`, as soon as `x`
has no pole at `P`. This is what makes the integral closure of `k[x]` in `F` — the affine model
attached to `x` — an object of the finite chart of `P`. -/
theorem mem_integers_of_isIntegral_adjoin {x : F} (hx : x ∈ P.integers) {y : F}
    (hy : IsIntegral (Algebra.adjoin k ({x} : Set F)) y) : y ∈ P.integers :=
  P.mem_integers_of_isIntegral
    (fun r ↦ P.adjoin_le_integers_iff.mpr hx r.1 r.2) hy

end Integers

section AffineModel

variable {R : Type w} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  (hR : ∀ r : R, algebraMap R F r ∈ P.integers)

include hR

/-- The **centre** on an affine model `R` of a place `P` finite on `R`: the height one prime of
`R` consisting of the elements with a zero at `P`. -/
def center : HeightOneSpectrum R :=
  P.valuation.heightOneSpectrum R fun r ↦ P.mem_integers_iff.mp (hR r)

/-- **The valuation of a place finite on an affine model is the adic valuation of its centre.**
This is the exact, not merely up-to-equivalence, form of the correspondence between places and
height one primes. -/
@[simp]
theorem valuation_center : (P.center hR).valuation F = P.valuation :=
  Valuation.valuation_heightOneSpectrum P.valuation_surjective _

/-- The centre of `P` on `R` consists of the elements of `R` at which the valuation of `P` is
`< 1`. -/
@[simp]
theorem mem_center_asIdeal {r : R} :
    r ∈ (P.center hR).asIdeal ↔ P.valuation (algebraMap R F r) < 1 := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), P.valuation_center hR]

/-- The additive form of `TauCeti.Place.mem_center_asIdeal`: the centre of `P` on `R` consists of
the elements of `R` with a zero at `P`. The hypothesis `r ≠ 0` guards the junk value
`ord_P 0 = 0`. -/
theorem mem_center_asIdeal_iff_ord_pos {r : R} (hr : r ≠ 0) :
    r ∈ (P.center hR).asIdeal ↔ 0 < P.ord (algebraMap R F r) := by
  have hr' : algebraMap R F r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
  rw [mem_center_asIdeal, P.valuation_eq_exp_neg_ord hr', ← WithZero.exp_zero (M := ℤ),
    WithZero.exp_lt_exp]
  omega

/-- **The coefficient formula at a place finite on an affine model**: the order at `P` of a
nonzero element of the model is the multiplicity of the centre of `P` in the ideal it generates.
This is what turns a divisor supported on the finite chart of a model into a factorization of
ideals. The hypothesis `r ≠ 0` guards the junk values `ord_P 0 = 0` and `mult_𝔭 ⊥ = 1`. -/
theorem ord_algebraMap_eq_multiplicity_center {r : R} (hr : r ≠ 0) :
    P.ord (algebraMap R F r) = multiplicity (P.center hR).asIdeal (Ideal.span {r}) := by
  have hr' : algebraMap R F r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
  rw [P.ord_eq_iff_valuation_eq_exp_neg hr', ← P.valuation_center hR,
    HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hr]

/-- A height one prime whose adic valuation is that of `P` is the centre of `P`. -/
theorem eq_center {𝔭 : HeightOneSpectrum R} (h : 𝔭.valuation F = P.valuation) :
    𝔭 = P.center hR :=
  Valuation.eq_heightOneSpectrum P.valuation_surjective _ h

/-- **A place of `F / k` whose valuation ring contains an affine model `R` is the adic place of a
unique height one prime of `R`** (Stichtenoth, Section III.2). -/
theorem existsUnique_valuation_eq :
    ∃! 𝔭 : HeightOneSpectrum R, 𝔭.valuation F = P.valuation :=
  Valuation.existsUnique_heightOneSpectrum_valuation_eq R P.valuation_surjective
    fun r ↦ P.mem_integers_iff.mp (hR r)

/-- The valuation ring of a place finite on an affine model is the localization of the model at
the centre of the place. -/
theorem valuationSubringAtPrime_eq_integers :
    HeightOneSpectrum.valuationSubringAtPrime F (P.center hR) = P.integers := by
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, P.valuation_center hR]
  exact SetLike.ext fun _ ↦ P.mem_integers_iff.symm

/-- Distinct places finite on an affine model have distinct centres: a place is recovered from its
centre. -/
theorem center_injective {Q : Place k F} (hQ : ∀ r : R, algebraMap R F r ∈ Q.integers)
    (h : P.center hR = Q.center hQ) : P = Q :=
  Place.ext (by rw [← P.valuation_center hR, ← Q.valuation_center hQ, h])

omit hR in
/-- A place at which `x` has no pole is the adic place of a unique height one prime of any affine
model integral over `k[x]`: the finite chart of `x` is covered by the height one primes of the
model. -/
theorem existsUnique_valuation_eq_of_isIntegral_adjoin {x : F} (hx : x ∈ P.integers)
    (hint : ∀ r : R, IsIntegral (Algebra.adjoin k ({x} : Set F)) (algebraMap R F r)) :
    ∃! 𝔭 : HeightOneSpectrum R, 𝔭.valuation F = P.valuation :=
  P.existsUnique_valuation_eq fun r ↦ P.mem_integers_of_isIntegral_adjoin hx (hint r)

end AffineModel

end Place

end TauCeti
