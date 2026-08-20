/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import TauCeti.FieldTheory.FunctionField.Place.Basic

/-!
# Places attached to the height-one primes of a Dedekind model

Let `k` be a field and `R` a Dedekind domain which is a `k`-algebra, with fraction field `F`.
Every height-one prime `p` of `R` gives a place of `F / k`: the normalized `p`-adic valuation
is surjective onto `ℤᵐ⁰` by `IsDedekindDomain.HeightOneSpectrum.valuation_surjective`, and it is
trivial on `k` because the nonzero constants are units of `R`. Distinct primes give distinct
places, and the residue field of the place is the residue field `R ⧸ p` of the prime, so the
degree of the place is `[R ⧸ p : k]`.

This is the affine half of the place vocabulary: applied to `R = k[X]` and `F = k(x)` it produces
the finite places of the rational function field (Stichtenoth, *Algebraic Function Fields and
Codes*, second edition, Proposition 1.2.1(a)), and applied to the integral closure of `k[x]` in a
function field it produces the places of a chosen affine model.

## Main definitions

* `TauCeti.Place.adic`: the place of `F / k` attached to `p : IsDedekindDomain.HeightOneSpectrum R`.
* `TauCeti.Place.integersAdicEquiv`: the valuation ring of that place is the localization of `R`
  at `p`.
* `TauCeti.Place.adicResidueHom`: reduction `R → F_P` at that place.

## Main results

* `TauCeti.Place.adic_injective`: distinct height-one primes give distinct places.
* `TauCeti.Place.adicResidueFieldEquiv`: the residue field of `Place.adic k F p` is `R ⧸ p`, as a
  `k`-algebra; `TauCeti.Place.adicResidueFieldEquiv_mk` computes this equivalence on quotient
  representatives, and `TauCeti.Place.degree_adic` reads off the degree of the place. The valuation
  ring of the place is the localization of `R` at `p`, so this is Mathlib's
  `IsLocalization.AtPrime.equivQuotMaximalIdeal`.
* `TauCeti.Place.ord_algebraMap_adic`: the order of `r : R` at the place is the multiplicity of
  `p` in `(r)`; `TauCeti.Place.isUniformizer_algebraMap_adic` specializes this to a generator of
  `p`, which is therefore a prime element for the place.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.1 and III.2.
* The adic valuation of a height-one prime, its valuation subring and the identification of that
  subring with the localization at the prime are
  `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` (María Inés de Frutos-Fernández); the
  residue field of a localization at a prime is
  `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`.
-/

public section

noncomputable section

open scoped WithZero

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable (k : Type*) (F : Type*) {R : Type*} [Field k] [Field F] [CommRing R]
  [IsDedekindDomain R] [Algebra k R] [Algebra R F] [IsFractionRing R F] [Algebra k F]
  [IsScalarTower k R F]

/-- The adic valuation of a height-one prime of a Dedekind `k`-algebra is trivial on `k`: a
nonzero constant is a unit of `R`, hence lies outside every prime ideal. -/
instance isTrivialOn_valuation (p : HeightOneSpectrum R) :
    (p.valuation F).IsTrivialOn k where
  eq_one c hc := by
    rw [IsScalarTower.algebraMap_apply k R F, valuation_eq_one_iff_notMem]
    exact fun hmem => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
      ((algebraMap k R).isUnit_map (isUnit_iff_ne_zero.2 hc)))

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti

universe u v w

variable (k : Type u) (F : Type v) {R : Type w} [Field k] [Field F] [CommRing R]
  [IsDedekindDomain R] [Algebra k R] [Algebra R F] [IsFractionRing R F] [Algebra k F]
  [IsScalarTower k R F]

namespace Place

/-- The place of `F / k` attached to a height-one prime `p` of a Dedekind `k`-algebra `R` with
fraction field `F`: the normalized `p`-adic valuation. -/
def adic (p : HeightOneSpectrum R) : Place k F where
  valuation := p.valuation F
  valuation_surjective := p.valuation_surjective F
  isTrivialOn := inferInstance

@[simp]
theorem valuation_adic (p : HeightOneSpectrum R) : (adic k F p).valuation = p.valuation F :=
  (rfl)

variable (p : HeightOneSpectrum R)

theorem integers_adic : (adic k F p).integers = HeightOneSpectrum.valuationSubringAtPrime F p := by
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  ext x
  rw [mem_integers_iff, valuation_adic, Valuation.mem_valuationSubring_iff]

/-- Distinct height-one primes give distinct places: the place remembers its prime. -/
theorem adic_injective : Function.Injective (adic k F (R := R)) := fun p q h => by
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) ?_
  rw [← valuation_adic k F p, ← valuation_adic k F q, h]

/-! ### Orders of elements of `R` -/

theorem algebraMap_mem_integers_adic (r : R) : algebraMap R F r ∈ (adic k F p).integers :=
  ((adic k F p).mem_integers_iff).mpr (by rw [valuation_adic]; exact p.valuation_le_one r)

theorem ord_algebraMap_adic_nonneg (r : R) : 0 ≤ (adic k F p).ord (algebraMap R F r) :=
  ((adic k F p).mem_integers_iff_ord_nonneg).mp (algebraMap_mem_integers_adic k F p r)

/-- An element of `R` has positive order at `adic k F p` exactly when it lies in `p`. -/
theorem ord_algebraMap_adic_pos_iff_mem {r : R} (hr : r ≠ 0) :
    0 < (adic k F p).ord (algebraMap R F r) ↔ r ∈ p.asIdeal := by
  have hr' : algebraMap R F r ≠ 0 := IsFractionRing.to_map_eq_zero_iff.ne.mpr hr
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), ← valuation_adic k F p,
    (adic k F p).valuation_eq_exp_neg_ord hr', ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

/-- The order of an element of `R` at the place `adic k F p` is the multiplicity of `p` in the
principal ideal it generates. -/
theorem ord_algebraMap_adic {r : R} (hr : r ≠ 0) :
    (adic k F p).ord (algebraMap R F r) = multiplicity p.asIdeal (Ideal.span {r}) := by
  have hr' : algebraMap R F r ≠ 0 := IsFractionRing.to_map_eq_zero_iff.ne.mpr hr
  rw [(adic k F p).ord_eq_iff_valuation_eq_exp_neg hr', valuation_adic,
    HeightOneSpectrum.valuation_of_algebraMap, p.intValuation_eq_exp_neg_multiplicity hr]

/-- A generator of `p` is a prime element for the place `adic k F p`, i.e. a uniformizer for its
normalized valuation. -/
theorem isUniformizer_algebraMap_adic {π : R} (h : p.asIdeal = Ideal.span {π}) :
    (adic k F p).valuation.IsUniformizer (algebraMap R F π) := by
  have hπ : π ≠ 0 := by
    rintro rfl
    exact p.ne_bot (by simp [h])
  have hπ' : algebraMap R F π ≠ 0 := IsFractionRing.to_map_eq_zero_iff.ne.mpr hπ
  rw [isUniformizer_iff_ord_eq_one, (adic k F p).ord_eq_iff_valuation_eq_exp_neg hπ',
    valuation_adic, HeightOneSpectrum.valuation_of_algebraMap,
    p.intValuation_singleton hπ h]

/-! ### The residue field -/

/-- `R` maps into the valuation ring of `adic k F p`, every element of `R` being integral there. -/
instance : Algebra R (adic k F p).integers :=
  ((algebraMap R F).codRestrict _ (algebraMap_mem_integers_adic k F p)).toAlgebra

instance : IsScalarTower R (adic k F p).integers F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : IsScalarTower k R (adic k F p).integers :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (IsScalarTower.algebraMap_apply k R F c)

/-- **The valuation ring of an adic place is the localization at its prime**, by
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring`. -/
def integersAdicEquiv :
    HeightOneSpectrum.valuationSubringAtPrime F p ≃ₐ[R] (adic k F p).integers :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (integers_adic k F p).symm)) fun _ => rfl

instance : IsLocalization.AtPrime ((adic k F p).integers) p.asIdeal :=
  IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl (integersAdicEquiv k F p)

/-- Reduction at the place `adic k F p`, as a ring homomorphism from `R` to its residue field. -/
def adicResidueHom : R →+* (adic k F p).ResidueField :=
  (IsLocalRing.residue _).comp (algebraMap R (adic k F p).integers)

variable {k F p}

theorem adicResidueHom_eq_zero_iff {r : R} :
    adicResidueHom k F p r = 0 ↔ r ∈ p.asIdeal := by
  rw [adicResidueHom, RingHom.comp_apply, residue_eq_zero_iff_valuation_lt_one, valuation_adic,
    ← ValuationSubring.algebraMap_apply, ← IsScalarTower.algebraMap_apply R _ F]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem p _

variable (k F p)

@[simp]
theorem adicResidueHom_algebraMap (c : k) :
    adicResidueHom k F p (algebraMap k R c) =
      algebraMap k (adic k F p).ResidueField c := by
  rw [adicResidueHom, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k R _,
    IsScalarTower.algebraMap_apply k (adic k F p).integers (adic k F p).ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]

/-- **The residue field of an adic place is the residue field of its prime**: reduction at
`adic k F p` identifies `R ⧸ p` with `F_P`, as `k`-algebras. Since the valuation ring of the place
is the localization of `R` at `p`, this is Mathlib's
`IsLocalization.AtPrime.equivQuotMaximalIdeal`, upgraded to a `k`-algebra equivalence. -/
def adicResidueFieldEquiv : (R ⧸ p.asIdeal) ≃ₐ[k] (adic k F p).ResidueField :=
  haveI := p.isMaximal
  AlgEquiv.ofRingEquiv
    (f := IsLocalization.AtPrime.equivQuotMaximalIdeal p.asIdeal ((adic k F p).integers))
    fun c =>
      (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk p.asIdeal _
        (algebraMap k R c)).trans (adicResidueHom_algebraMap k F p c)

@[simp]
theorem adicResidueFieldEquiv_mk (r : R) :
    adicResidueFieldEquiv k F p (Ideal.Quotient.mk p.asIdeal r) = adicResidueHom k F p r :=
  have := p.isMaximal
  IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk p.asIdeal ((adic k F p).integers) r

/-- The degree of an adic place is the degree of the residue field of its prime. -/
theorem degree_adic : (adic k F p).degree = Module.finrank k (R ⧸ p.asIdeal) := by
  rw [degree_eq_finrank, ← (adicResidueFieldEquiv k F p).toLinearEquiv.finrank_eq]

instance finiteDimensional_residueField_adic [Module.Finite k (R ⧸ p.asIdeal)] :
    Module.Finite k (adic k F p).ResidueField :=
  Module.Finite.equiv (adicResidueFieldEquiv k F p).toLinearEquiv

end Place

end TauCeti
