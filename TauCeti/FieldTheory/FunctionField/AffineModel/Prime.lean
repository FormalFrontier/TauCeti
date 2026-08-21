/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `TauCeti.Place.residueHom`: evaluation of the elements of the model at a place finite on it, a
  `k`-algebra map `R → F_P` whose kernel is the centre of the place
  (`TauCeti.Place.ker_residueHom`).
* `TauCeti.Place.heightOneSpectrumEquiv`: the bijection between the places finite on a model and
  the height one primes of the model.

## Main results

* `TauCeti.Place.center_ofPrime` and `TauCeti.Place.ofPrime_center`: the two constructions are
  mutually inverse, and `TauCeti.Place.exists_eq_ofPrime_iff` identifies the places in the image
  as exactly the places finite on the model.
* `TauCeti.Place.ord_ofPrime_algebraMap`: the coefficient formula `ord_P r = mult_𝔭 (r)`, for
  `r ≠ 0`, the `𝔭`-form of `TauCeti.Place.ord_algebraMap_eq_multiplicity_center`.
* `TauCeti.Place.quotientAlgEquivResidueField`: the residue field of a place finite on the model
  is `R` modulo the centre of the place, whence `TauCeti.Place.degree_eq_finrank_quotient_center`;
  `TauCeti.Place.quotientAlgEquivResidueFieldOfPrime` and `TauCeti.Place.degree_ofPrime` are the
  `𝔭`-forms, `F_P = R ⧸ 𝔭` and `deg P = [R ⧸ 𝔭 : k]`.

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
    exact Ideal.notMem_of_isUnit _ ((isUnit_iff_ne_zero.mpr hc).map (algebraMap k R))⟩

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
theorem coe_heightOneSpectrumEquiv_symm_apply (𝔭 : HeightOneSpectrum R) :
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

/-- **The coefficient formula on the finite chart**: the order at the place of `𝔭` of a nonzero
element of the model is the multiplicity of `𝔭` in the ideal it generates. This is
`TauCeti.Place.ord_algebraMap_eq_multiplicity_center` at the place of `𝔭`, whose centre is `𝔭`,
and it is what turns a divisor supported on the finite chart into a factorization of ideals. -/
theorem ord_ofPrime_algebraMap (𝔭 : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    (ofPrime k F 𝔭).ord (algebraMap R F r) = multiplicity 𝔭.asIdeal (Ideal.span {r}) := by
  rw [(ofPrime k F 𝔭).ord_algebraMap_eq_multiplicity_center
    (algebraMap_mem_integers_ofPrime k F 𝔭) hr, center_ofPrime]

end Correspondence

section ResidueField

variable (P : Place k F) (hR : ∀ r : R, algebraMap R F r ∈ P.integers)

include hR

/-- **Evaluation of the elements of an affine model at a place finite on it**, as a map of
`k`-algebras `R → F_P`. It is surjective with kernel the centre of the place, which is the
content of `TauCeti.Place.quotientAlgEquivResidueField`. -/
noncomputable def residueHom : R →ₐ[k] P.ResidueField :=
  { (IsLocalRing.residue P.integers).comp ((algebraMap R F).codRestrict P.integers hR) with
    commutes' := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply k P.integers P.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
      exact congrArg (IsLocalRing.residue _)
        (Subtype.ext (IsScalarTower.algebraMap_apply k R F c).symm) }

omit [IsDedekindDomain R] [IsFractionRing R F] in
@[simp]
theorem residueHom_apply (r : R) :
    P.residueHom hR r = IsLocalRing.residue P.integers ⟨algebraMap R F r, hR r⟩ := (rfl)

/-- **The kernel of evaluation at `P` is the centre of `P` on the model**: this is the
evaluation-map form of `TauCeti.Place.mem_center_asIdeal`, which says the same thing about the
valuation of `P`. -/
@[simp]
theorem ker_residueHom : RingHom.ker (P.residueHom hR) = (P.center hR).asIdeal := by
  ext r
  rw [RingHom.mem_ker, residueHom_apply, P.residue_eq_zero_iff_valuation_lt_one,
    P.mem_center_asIdeal hR]

/-- **Every residue at a place finite on an affine model is the residue of an element of the
model.** This is Mathlib's approximation theorem for the adic valuation of the centre, at the
accuracy `1`: a function integral at the place is within `1` of an element of the model, so the
two have the same residue. -/
theorem residueHom_surjective : Function.Surjective (P.residueHom hR) := by
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (P.center hR)
    (by rw [P.valuation_center hR]; exact P.mem_integers_iff.mp a.2) 1
  rw [Units.val_one, P.valuation_center hR] at hc
  refine ⟨c, ?_⟩
  rw [residueHom_apply, ← sub_eq_zero, ← map_sub, P.residue_eq_zero_iff_valuation_lt_one]
  push_cast
  exact hc

/-- **The residue field of a place finite on an affine model is the model modulo the centre of
the place**, as `k`-algebras. -/
noncomputable def quotientAlgEquivResidueField :
    (R ⧸ (P.center hR).asIdeal) ≃ₐ[k] P.ResidueField :=
  (Ideal.quotientEquivAlgOfEq k (P.ker_residueHom hR).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (P.residueHom_surjective hR))

@[simp]
theorem quotientAlgEquivResidueField_mk (r : R) :
    P.quotientAlgEquivResidueField hR (Ideal.Quotient.mk (P.center hR).asIdeal r)
      = P.residueHom hR r := (rfl)

/-- **The degree of a place finite on an affine model is the residue degree of its centre**: the
weight a divisor attaches to a place of the finite chart is the one Mathlib's ideal theory
attaches to the corresponding prime. -/
theorem degree_eq_finrank_quotient_center :
    P.degree = Module.finrank k (R ⧸ (P.center hR).asIdeal) := by
  rw [P.degree_eq_finrank]
  exact ((P.quotientAlgEquivResidueField hR).toLinearEquiv.finrank_eq).symm

end ResidueField

section ResidueFieldOfPrime

variable (k F) (𝔭 : HeightOneSpectrum R)

/-- **The residue field of the place of a height one prime `𝔭` of an affine model is `R ⧸ 𝔭`**,
as `k`-algebras: this is `TauCeti.Place.quotientAlgEquivResidueField` at the place of `𝔭`, whose
centre is `𝔭`. -/
noncomputable def quotientAlgEquivResidueFieldOfPrime :
    (R ⧸ 𝔭.asIdeal) ≃ₐ[k] (ofPrime k F 𝔭).ResidueField :=
  (Ideal.quotientEquivAlgOfEq k
      (congrArg HeightOneSpectrum.asIdeal (center_ofPrime k F 𝔭)).symm).trans
    ((ofPrime k F 𝔭).quotientAlgEquivResidueField (algebraMap_mem_integers_ofPrime k F 𝔭))

@[simp]
theorem quotientAlgEquivResidueFieldOfPrime_mk (r : R) :
    quotientAlgEquivResidueFieldOfPrime k F 𝔭 (Ideal.Quotient.mk 𝔭.asIdeal r)
      = (ofPrime k F 𝔭).residueHom (algebraMap_mem_integers_ofPrime k F 𝔭) r := (rfl)

/-- **The degree of the place of `𝔭` is the residue degree of `𝔭`**: the weight a divisor
attaches to a place of the finite chart is the one Mathlib's ideal theory attaches to the
corresponding prime. -/
theorem degree_ofPrime : (ofPrime k F 𝔭).degree = Module.finrank k (R ⧸ 𝔭.asIdeal) := by
  rw [(ofPrime k F 𝔭).degree_eq_finrank_quotient_center (algebraMap_mem_integers_ofPrime k F 𝔭),
    center_ofPrime]

end ResidueFieldOfPrime

end Place

end TauCeti
