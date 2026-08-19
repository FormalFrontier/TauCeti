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
* `TauCeti.Place.adicResidueHom`: reduction `R → F_P` at that place.

## Main results

* `TauCeti.Place.adic_injective`: distinct height-one primes give distinct places.
* `TauCeti.Place.adicResidueFieldEquiv`: the residue field of `Place.adic k F p` is `R ⧸ p`, as a
  `k`-algebra; `TauCeti.Place.adicResidueFieldEquiv_mk` computes this equivalence on quotient
  representatives, and `TauCeti.Place.degree_adic` reads off the degree of the place.
* `TauCeti.Place.ord_algebraMap_adic`: the order of `r : R` at the place is the multiplicity of
  `p` in `(r)`; `TauCeti.Place.isUniformizer_adic_algebraMap` specializes this to a generator of
  `p`, which is therefore a prime element for the place.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.1 and III.2.
-/

public section

noncomputable section

open scoped WithZero

open IsDedekindDomain

namespace TauCeti

universe u v w

variable (k : Type u) (F : Type v) {R : Type w} [Field k] [Field F] [CommRing R]
  [IsDedekindDomain R] [Algebra k R] [Algebra R F] [IsFractionRing R F] [Algebra k F]
  [IsScalarTower k R F]

namespace Place

/-- The adic valuation of a height-one prime of a Dedekind `k`-algebra is trivial on `k`: a
nonzero constant is a unit of `R`, hence lies outside every prime ideal. -/
theorem isTrivialOn_adicValuation (p : HeightOneSpectrum R) :
    (p.valuation F).IsTrivialOn k where
  eq_one c hc := by
    rw [IsScalarTower.algebraMap_apply k R F, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun hmem => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
      ((algebraMap k R).isUnit_map (isUnit_iff_ne_zero.2 hc)))

/-- The place of `F / k` attached to a height-one prime `p` of a Dedekind `k`-algebra `R` with
fraction field `F`: the normalized `p`-adic valuation. -/
def adic (p : HeightOneSpectrum R) : Place k F where
  valuation := p.valuation F
  valuation_surjective := p.valuation_surjective F
  isTrivialOn := isTrivialOn_adicValuation k F p

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
  have hr' : algebraMap R F r ≠ 0 := fun h => hr (IsFractionRing.injective R F (by simpa using h))
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), ← valuation_adic k F p,
    (adic k F p).valuation_eq_exp_neg_ord hr', ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

/-- The order of an element of `R` at the place `adic k F p` is the multiplicity of `p` in the
principal ideal it generates. -/
theorem ord_algebraMap_adic {r : R} (hr : r ≠ 0) :
    (adic k F p).ord (algebraMap R F r) = multiplicity p.asIdeal (Ideal.span {r}) := by
  have hr' : algebraMap R F r ≠ 0 := fun h => hr (IsFractionRing.injective R F (by simpa using h))
  rw [(adic k F p).ord_eq_iff_valuation_eq_exp_neg hr', valuation_adic,
    HeightOneSpectrum.valuation_of_algebraMap, p.intValuation_eq_exp_neg_multiplicity hr]

/-- A generator of `p` is a prime element for the place `adic k F p`, i.e. a uniformizer for its
normalized valuation. -/
theorem isUniformizer_adic_algebraMap {π : R} (hπ : π ≠ 0) (h : p.asIdeal = Ideal.span {π}) :
    (adic k F p).valuation.IsUniformizer (algebraMap R F π) := by
  have hπ' : algebraMap R F π ≠ 0 := fun h => hπ (IsFractionRing.injective R F (by simpa using h))
  rw [isUniformizer_iff_ord_eq_one, (adic k F p).ord_eq_iff_valuation_eq_exp_neg hπ',
    valuation_adic, HeightOneSpectrum.valuation_of_algebraMap,
    p.intValuation_singleton hπ h]

/-! ### The residue field -/

/-- The canonical map from `R` to the valuation ring of the place `adic k F p`. -/
def adicIntegersHom : R →+* (adic k F p).integers :=
  (algebraMap R F).codRestrict _ (algebraMap_mem_integers_adic k F p)

@[simp]
theorem coe_adicIntegersHom (r : R) : (adicIntegersHom k F p r : F) = algebraMap R F r := (rfl)

/-- Reduction at the place `adic k F p`, as a ring homomorphism from `R` to its residue field. -/
def adicResidueHom : R →+* (adic k F p).ResidueField :=
  (IsLocalRing.residue _).comp (adicIntegersHom k F p)

variable {k F p}

theorem adicResidueHom_eq_zero_iff {r : R} :
    adicResidueHom k F p r = 0 ↔ r ∈ p.asIdeal := by
  rw [adicResidueHom, RingHom.comp_apply, residue_eq_zero_iff_valuation_lt_one, valuation_adic]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem p _

variable (k F p)

theorem ker_adicResidueHom : RingHom.ker (adicResidueHom k F p) = p.asIdeal :=
  Ideal.ext fun _ => adicResidueHom_eq_zero_iff

/-- Reduction at `adic k F p` is surjective onto the residue field: the valuation ring of the
place is the localization of `R` at `p`, and a denominator outside `p` can be inverted modulo
`p`. -/
theorem adicResidueHom_surjective : Function.Surjective (adicResidueHom k F p) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : (x : F) ∈ HeightOneSpectrum.valuationSubringAtPrime F p := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact ((adic k F p).mem_integers_iff).mp x.2
  obtain ⟨a, s, hs, hxs⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ p.asIdeal.zero_mem)
  have hsF : algebraMap R F s ≠ 0 := fun h =>
    hs0 ((IsFractionRing.injective R F) (by simpa using h))
  obtain ⟨u, c, hc, huc⟩ := Ideal.IsMaximal.exists_inv (p.isMaximal) hs
  have hmem : a * u * s - a ∈ p.asIdeal := by
    have h : a * u * s - a = -(a * c) := by
      rw [neg_mul_eq_mul_neg, eq_comm, ← sub_eq_iff_eq_add'.mpr huc.symm]
      ring
    rw [h]
    exact p.asIdeal.neg_mem (p.asIdeal.mul_mem_left a hc)
  refine ⟨a * u, ?_⟩
  rw [adicResidueHom, RingHom.comp_apply, ← sub_eq_zero, ← _root_.map_sub,
    IsLocalRing.residue_eq_zero_iff, (adic k F p).mem_maximalIdeal_iff_valuation_lt_one,
    valuation_adic]
  have hval : ((adicIntegersHom k F p (a * u) - x : (adic k F p).integers) : F)
      = algebraMap R F (a * u * s - a) * (algebraMap R F s)⁻¹ := by
    push_cast [hxs, coe_adicIntegersHom]
    field_simp
  rw [hval, _root_.map_mul, map_inv₀,
    (HeightOneSpectrum.valuation_eq_one_iff_notMem p (K := F)).mpr hs, inv_one, mul_one]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem p _).mpr hmem

@[simp]
theorem adicResidueHom_algebraMap (c : k) :
    adicResidueHom k F p (algebraMap k R c) =
      algebraMap k (adic k F p).ResidueField c := by
  rw [adicResidueHom, RingHom.comp_apply]
  have h : adicIntegersHom k F p (algebraMap k R c) =
      algebraMap k (adic k F p).integers c :=
    Subtype.ext (by rw [coe_adicIntegersHom, ← IsScalarTower.algebraMap_apply]; rfl)
  rw [h]
  rfl

/-- **The residue field of an adic place is the residue field of its prime**: reduction at
`adic k F p` identifies `R ⧸ p` with `F_P`, as `k`-algebras. -/
def adicResidueFieldEquiv : (R ⧸ p.asIdeal) ≃ₐ[k] (adic k F p).ResidueField :=
  AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq (ker_adicResidueHom k F p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (adicResidueHom_surjective k F p)))
    fun c => by
      simpa only [AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
        ← Ideal.Quotient.mk_algebraMap, Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk] using adicResidueHom_algebraMap k F p c

@[simp]
theorem adicResidueFieldEquiv_mk (r : R) :
    adicResidueFieldEquiv k F p (Ideal.Quotient.mk p.asIdeal r) = adicResidueHom k F p r := by
  rw [adicResidueFieldEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- The degree of an adic place is the degree of the residue field of its prime. -/
theorem degree_adic : (adic k F p).degree = Module.finrank k (R ⧸ p.asIdeal) := by
  rw [degree_eq_finrank, ← (adicResidueFieldEquiv k F p).toLinearEquiv.finrank_eq]

theorem finite_residueField_adic [Module.Finite k (R ⧸ p.asIdeal)] :
    Module.Finite k (adic k F p).ResidueField :=
  Module.Finite.equiv (adicResidueFieldEquiv k F p).toLinearEquiv

end Place

end TauCeti
