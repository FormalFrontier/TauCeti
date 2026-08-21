/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.FieldTheory.FunctionField.AffineModel.Place

/-!
# Affine models: the place of a height one prime, and the two-way correspondence

An *affine model* of `F / k` is a Dedekind `k`-subalgebra `R` of `F` whose fraction field is `F`.
`TauCeti/FieldTheory/FunctionField/AffineModel/Place.lean` sends a place of `F / k` that is finite
on `R` to a height one prime of `R`, its centre. This file supplies the other direction: the
normalized `𝔭`-adic valuation of `F` attached to a height one prime `𝔭` of `R` is trivial on the
constants — every nonzero constant is a unit of `R`, hence lies outside `𝔭` — so it *is* a place
of `F / k`. The two constructions are mutually inverse, which packages the correspondence as a
bijection

`{P : Place k F | R ⊆ 𝒪_P} ≃ HeightOneSpectrum R`.

The correspondence is then made quantitative. On `R` the order function of the place of `𝔭` is
the multiplicity of `𝔭` in a principal ideal, so divisor coefficients on the finite chart are read
off from Mathlib's factorization calculus; and the residue field of the place of `𝔭` is `R ⧸ 𝔭`,
so the degree of the place is the residue degree `[R ⧸ 𝔭 : k]` of the prime. Together these say
that divisor theory on the finite chart of a model is exactly the ideal theory of the model.

## Main definitions

* `TauCeti.Place.ofPrime`: the place of `F / k` attached to a height one prime of an affine
  model.
* `TauCeti.Place.residueHomOfPrime`: evaluation of the elements of the model at that place, a
  `k`-algebra map `R → F_P` with kernel `𝔭` (`TauCeti.Place.ker_residueHomOfPrime`).
* `TauCeti.Place.heightOneSpectrumEquiv`: the bijection between the places finite on a model and
  the height one primes of the model.

## Main results

* `TauCeti.Place.center_ofPrime` and `TauCeti.Place.ofPrime_center`: the two constructions are
  mutually inverse, and `TauCeti.Place.exists_eq_ofPrime_iff` identifies the places in the image
  as exactly the places finite on the model.
* `TauCeti.Place.ord_ofPrime_algebraMap`: the coefficient formula `ord_P r = mult_𝔭 (r)`.
* `TauCeti.Place.residueFieldAlgEquivOfPrime`: the residue field of the place of `𝔭` is `R ⧸ 𝔭`,
  whence `TauCeti.Place.degree_ofPrime`: `deg P = [R ⧸ 𝔭 : k]`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.1 and III.2.
-/

public section

open IsDedekindDomain

namespace TauCeti

namespace Place

universe u v w

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
  {R : Type w} [CommRing R] [IsDedekindDomain R] [Algebra k R] [Algebra R F]
  [IsScalarTower k R F] [IsFractionRing R F]

section OfPrime

variable (k F)

/-- **The place of `F / k` attached to a height one prime `𝔭` of an affine model `R`**: its
valuation is Mathlib's normalized `𝔭`-adic valuation of `F`. Triviality on the constants is the
only thing to check, and it holds because a nonzero constant is a unit of `R` and therefore
avoids `𝔭`. -/
noncomputable def ofPrime (𝔭 : HeightOneSpectrum R) : Place k F where
  valuation := 𝔭.valuation F
  valuation_surjective := 𝔭.valuation_surjective F
  isTrivialOn := ⟨fun c hc ↦ by
    rw [IsScalarTower.algebraMap_apply k R F, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun h ↦ 𝔭.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (isUnit_iff_exists_inv.mpr ⟨algebraMap k R c⁻¹, by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]⟩))⟩

variable (𝔭 : HeightOneSpectrum R)

@[simp]
theorem valuation_ofPrime : (ofPrime k F 𝔭).valuation = 𝔭.valuation F := (rfl)

/-- An affine model is contained in the valuation ring of the place of each of its height one
primes: the place of `𝔭` is finite on `R`. -/
theorem algebraMap_mem_integers_ofPrime (r : R) :
    algebraMap R F r ∈ (ofPrime k F 𝔭).integers :=
  (ofPrime k F 𝔭).mem_integers_iff.mpr (by rw [valuation_ofPrime]; exact 𝔭.valuation_le_one r)

/-- The valuation of the place of `𝔭` extends the `𝔭`-adic valuation of the model. -/
theorem valuation_ofPrime_algebraMap (r : R) :
    (ofPrime k F 𝔭).valuation (algebraMap R F r) = 𝔭.intValuation r := by
  rw [valuation_ofPrime, HeightOneSpectrum.valuation_of_algebraMap]

/-- The elements of the model with a zero at the place of `𝔭` are exactly the elements of `𝔭`. -/
theorem valuation_ofPrime_algebraMap_lt_one_iff {r : R} :
    (ofPrime k F 𝔭).valuation (algebraMap R F r) < 1 ↔ r ∈ 𝔭.asIdeal := by
  rw [valuation_ofPrime, HeightOneSpectrum.valuation_lt_one_iff_mem]

/-- **The coefficient formula on the finite chart**: the order at the place of `𝔭` of an element
of the model is the multiplicity of `𝔭` in the ideal it generates. This is what turns a divisor
supported on the finite chart into a factorization of ideals. -/
theorem ord_ofPrime_algebraMap {r : R} (hr : r ≠ 0) :
    (ofPrime k F 𝔭).ord (algebraMap R F r) = multiplicity 𝔭.asIdeal (Ideal.span {r}) := by
  have hr' : algebraMap R F r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
  rw [(ofPrime k F 𝔭).ord_eq_iff_valuation_eq_exp_neg hr', valuation_ofPrime_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity 𝔭 hr]

end OfPrime

section Correspondence

variable (k F)

/-- The centre on `R` of the place of a height one prime `𝔭` of `R` is `𝔭` itself. -/
@[simp]
theorem center_ofPrime (𝔭 : HeightOneSpectrum R) :
    (ofPrime k F 𝔭).center (algebraMap_mem_integers_ofPrime k F 𝔭) = 𝔭 :=
  ((ofPrime k F 𝔭).eq_center _ (valuation_ofPrime k F 𝔭).symm).symm

/-- The place of the centre on `R` of a place finite on `R` is that place. -/
@[simp]
theorem ofPrime_center (P : Place k F) (hR : ∀ r : R, algebraMap R F r ∈ P.integers) :
    ofPrime k F (P.center hR) = P :=
  Place.ext (by rw [valuation_ofPrime, P.valuation_center hR])

/-- The valuation ring of the place of `𝔭` is the localization of the model at `𝔭`. -/
theorem valuationSubringAtPrime_eq_integers_ofPrime (𝔭 : HeightOneSpectrum R) :
    HeightOneSpectrum.valuationSubringAtPrime F 𝔭 = (ofPrime k F 𝔭).integers := by
  have h := (ofPrime k F 𝔭).valuationSubringAtPrime_eq_integers
    (algebraMap_mem_integers_ofPrime k F 𝔭)
  rwa [center_ofPrime] at h

variable (R) in
/-- **The places of `F / k` finite on an affine model `R` are exactly the height one primes of
`R`** (Stichtenoth, Section III.2): the centre of a place and the adic place of a prime are
mutually inverse bijections. -/
noncomputable def heightOneSpectrumEquiv :
    {P : Place k F // ∀ r : R, algebraMap R F r ∈ P.integers} ≃ HeightOneSpectrum R where
  toFun P := P.1.center P.2
  invFun 𝔭 := ⟨ofPrime k F 𝔭, algebraMap_mem_integers_ofPrime k F 𝔭⟩
  left_inv P := Subtype.ext (ofPrime_center k F P.1 P.2)
  right_inv 𝔭 := center_ofPrime k F 𝔭

@[simp]
theorem heightOneSpectrumEquiv_apply
    (P : {P : Place k F // ∀ r : R, algebraMap R F r ∈ P.integers}) :
    heightOneSpectrumEquiv k F R P = P.1.center P.2 := (rfl)

@[simp]
theorem heightOneSpectrumEquiv_symm_apply (𝔭 : HeightOneSpectrum R) :
    ((heightOneSpectrumEquiv k F R).symm 𝔭).1 = ofPrime k F 𝔭 := (rfl)

/-- Distinct height one primes of a model give distinct places. -/
theorem ofPrime_injective : Function.Injective (ofPrime (R := R) k F) := fun 𝔭 𝔮 h ↦
  HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F)
    (by rw [← valuation_ofPrime k F 𝔭, ← valuation_ofPrime k F 𝔮, h])

/-- **A place of `F / k` is the place of a height one prime of an affine model `R` exactly when
it is finite on `R`**: the image of `TauCeti.Place.ofPrime` is the finite chart of the model. -/
theorem exists_eq_ofPrime_iff (P : Place k F) :
    (∃ 𝔭 : HeightOneSpectrum R, ofPrime k F 𝔭 = P) ↔ ∀ r : R, algebraMap R F r ∈ P.integers :=
  ⟨fun ⟨𝔭, h⟩ r ↦ h ▸ algebraMap_mem_integers_ofPrime k F 𝔭 r,
    fun hR ↦ ⟨P.center hR, ofPrime_center k F P hR⟩⟩

end Correspondence

section ResidueField

variable (k F) (𝔭 : HeightOneSpectrum R)

/-- The elements of an affine model, viewed inside the valuation ring of the place of one of its
height one primes. -/
noncomputable def toIntegersOfPrime : R →+* (ofPrime k F 𝔭).integers :=
  (algebraMap R F).codRestrict _ (algebraMap_mem_integers_ofPrime k F 𝔭)

@[simp]
theorem coe_toIntegersOfPrime (r : R) :
    (toIntegersOfPrime k F 𝔭 r : F) = algebraMap R F r := (rfl)

/-- **Evaluation of the elements of an affine model at the place of one of its height one
primes**, as a map of `k`-algebras `R → F_P`. It is surjective with kernel `𝔭`, which is the
content of `TauCeti.Place.residueFieldAlgEquivOfPrime`. -/
noncomputable def residueHomOfPrime : R →ₐ[k] (ofPrime k F 𝔭).ResidueField :=
  { (IsLocalRing.residue (ofPrime k F 𝔭).integers).comp (toIntegersOfPrime k F 𝔭) with
    commutes' := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply k (ofPrime k F 𝔭).integers (ofPrime k F 𝔭).ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
      exact congrArg (IsLocalRing.residue _)
        (Subtype.ext (IsScalarTower.algebraMap_apply k R F c).symm) }

theorem residueHomOfPrime_apply (r : R) : residueHomOfPrime k F 𝔭 r =
    IsLocalRing.residue (ofPrime k F 𝔭).integers (toIntegersOfPrime k F 𝔭 r) := (rfl)

/-- **The elements of the model that vanish at the place of `𝔭` are exactly the elements of
`𝔭`.** -/
theorem ker_residueHomOfPrime : RingHom.ker (residueHomOfPrime k F 𝔭) = 𝔭.asIdeal := by
  ext r
  rw [RingHom.mem_ker, residueHomOfPrime_apply,
    (ofPrime k F 𝔭).residue_eq_zero_iff_valuation_lt_one, coe_toIntegersOfPrime,
    valuation_ofPrime_algebraMap_lt_one_iff]

/-- **Every residue at the place of `𝔭` is the residue of an element of the model.** A function
integral at the place is a fraction `n / d` of elements of the model with `d ∉ 𝔭`; inverting `d`
in the field `R ⧸ 𝔭` produces an element of `R` with the same residue. -/
theorem residueHomOfPrime_surjective : Function.Surjective (residueHomOfPrime k F 𝔭) := by
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer 𝔭 (a : F)
    (by rw [← valuation_ofPrime k F 𝔭]; exact (ofPrime k F 𝔭).mem_integers_iff.mp a.2)
  obtain ⟨c, hmem⟩ : ∃ c : R, n - (d : R) * c ∈ 𝔭.asIdeal := by
    obtain ⟨y, i, hi, hyd⟩ := 𝔭.isMaximal.exists_inv d.2
    refine ⟨y * n, ?_⟩
    have h : n - (d : R) * (y * n) = i * n := by linear_combination (-n) * hyd
    exact h ▸ Ideal.mul_mem_right n _ hi
  refine ⟨c, ?_⟩
  have hcoe : ((a - toIntegersOfPrime k F 𝔭 c : (ofPrime k F 𝔭).integers) : F)
      = (a : F) - algebraMap R F c := by
    push_cast
    rw [coe_toIntegersOfPrime]
  have hdval : (ofPrime k F 𝔭).valuation (algebraMap R F (d : R)) = 1 := by
    rw [valuation_ofPrime, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact d.2
  have hprod : ((a : F) - algebraMap R F c) * algebraMap R F (d : R)
      = algebraMap R F (n - (d : R) * c) := by
    rw [map_sub, map_mul, sub_mul, hnd]
    ring
  have hzero : IsLocalRing.residue (ofPrime k F 𝔭).integers
      (a - toIntegersOfPrime k F 𝔭 c) = 0 := by
    rw [(ofPrime k F 𝔭).residue_eq_zero_iff_valuation_lt_one]
    calc (ofPrime k F 𝔭).valuation ((a - toIntegersOfPrime k F 𝔭 c : (ofPrime k F 𝔭).integers) : F)
        = (ofPrime k F 𝔭).valuation ((a : F) - algebraMap R F c) *
            (ofPrime k F 𝔭).valuation (algebraMap R F (d : R)) := by rw [hcoe, hdval, mul_one]
      _ = (ofPrime k F 𝔭).valuation (algebraMap R F (n - (d : R) * c)) := by
            rw [← map_mul, hprod]
      _ < 1 := (valuation_ofPrime_algebraMap_lt_one_iff k F 𝔭).mpr hmem
  rw [residueHomOfPrime_apply]
  exact (sub_eq_zero.mp (by rwa [map_sub] at hzero)).symm

/-- **The residue field of the place of a height one prime `𝔭` of an affine model is `R ⧸ 𝔭`**,
as `k`-algebras. -/
noncomputable def residueFieldAlgEquivOfPrime :
    (R ⧸ 𝔭.asIdeal) ≃ₐ[k] (ofPrime k F 𝔭).ResidueField :=
  (Ideal.quotientEquivAlgOfEq k (ker_residueHomOfPrime k F 𝔭).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (residueHomOfPrime_surjective k F 𝔭))

@[simp]
theorem residueFieldAlgEquivOfPrime_mk (r : R) :
    residueFieldAlgEquivOfPrime k F 𝔭 (Ideal.Quotient.mk 𝔭.asIdeal r)
      = residueHomOfPrime k F 𝔭 r := (rfl)

/-- **The degree of the place of `𝔭` is the residue degree of `𝔭`**: the weight a divisor
attaches to a place of the finite chart is the one Mathlib's ideal theory attaches to the
corresponding prime. -/
theorem degree_ofPrime : (ofPrime k F 𝔭).degree = Module.finrank k (R ⧸ 𝔭.asIdeal) := by
  rw [(ofPrime k F 𝔭).degree_eq_finrank]
  exact ((residueFieldAlgEquivOfPrime k F 𝔭).toLinearEquiv.finrank_eq).symm

/-- The degree of a place finite on an affine model is the residue degree of its centre. -/
theorem degree_eq_finrank_quotient_center (P : Place k F)
    (hR : ∀ r : R, algebraMap R F r ∈ P.integers) :
    P.degree = Module.finrank k (R ⧸ (P.center hR).asIdeal) := by
  conv_lhs => rw [← ofPrime_center k F P hR]
  exact degree_ofPrime k F (P.center hR)

end ResidueField

end Place

end TauCeti
