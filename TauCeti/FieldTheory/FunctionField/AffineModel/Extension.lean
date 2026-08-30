/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.RamificationInertia.Basic
public import TauCeti.FieldTheory.FunctionField.AffineModel.Prime
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre

/-!
# Affine models of an extension: the fundamental identity

Let `F' / k'` be a finite extension of the field extension `F / k`, let `R` be an affine model of
`F / k` and let `S` be an affine model of `F' / k'` that is an `R`-algebra: a pair of charts of the
two curves, compatible with the covering map. This file identifies the extension-theoretic data of
a place of `F' / k'` finite on `S` with Mathlib's ideal-theoretic data of its centre, and deduces
the **fundamental identity** `∑_{P' ∣ P} e(P' ∣ P) · f(P' ∣ P) = [F' : F]` at every place of the
finite chart, supplying the inequality of
`TauCeti/FieldTheory/FunctionField/Place/Extension/Fibre.lean` with its converse.

The dictionary is exact at each of the three items. The centre on `S` of a place of `F' / k'` lies
over the centre on `R` of the place of `F / k` it restricts to; the ramification index `e(P' ∣ P)`,
defined as the factor by which the order function scales, is `Ideal.ramificationIdx`, because
Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` scales the adic valuations by
exactly that factor; and the relative degree `f(P' ∣ P) = [F'_{P'} : F_P]` is `Ideal.inertiaDeg`,
because the residue field of a place finite on a model is the model modulo the centre, compatibly
on both levels. Summing over the fibre is then Mathlib's
`Ideal.sum_ramification_inertia_eq_finrank` for the finite extension of Dedekind domains `S / R`,
transported to the fraction fields.

The identity is stated at the place of a height one prime of `R`; the places outside the finite
chart of `R` are reached by the same statement at a second model, as in Stichtenoth's two-chart
device.

## Main definitions

* `TauCeti.Place.restrictOfPrimeEquivPrimesOver`: the places of `F' / k'` lying over the place of a
  height one prime `𝔭` of `R` are exactly the primes of `S` lying over `𝔭`.

## Main results

* `TauCeti.Place.center_liesOver`: the centre on `S` of a place of `F' / k'` finite on `S` lies
  over the centre on `R` of its restriction to `F`.
* `TauCeti.Place.ramificationIdx_eq_ramificationIdx_center` and
  `TauCeti.Place.relativeDegree_eq_inertiaDeg_center`: the two bridge lemmas
  `e(P' ∣ P) = Ideal.ramificationIdx` and `f(P' ∣ P) = Ideal.inertiaDeg`, with
  `TauCeti.Place.ramificationIdx_ofPrime` and `TauCeti.Place.relativeDegree_ofPrime` their forms at
  the place of a height one prime of `S`.
* `TauCeti.Place.restrict_ofPrime`: the place of a prime `𝔓` of `S` lies over the place of a prime
  `𝔭` of `R` as soon as `𝔓` lies over `𝔭`.
* `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank`: **the fundamental identity**
  (Stichtenoth, Theorem 3.1.11) at a place of the finite chart.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections III.1 and III.2.
-/

public section

open IsDedekindDomain

namespace TauCeti

namespace Place

universe u u' v v' w w'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable {R : Type w} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable {S : Type w'} [CommRing S] [IsDedekindDomain S] [Algebra S F'] [IsFractionRing S F']
variable [Algebra R S] [Algebra R F'] [IsScalarTower R S F'] [IsScalarTower R F F']

section Chart

include F F'

omit [IsFractionRing S F'] in
/-- `S` is torsion free over `R`, a hypothesis of Mathlib's ideal-theoretic ramification API. `R`
injects into `S` because both routes from `R` to `F'` are injective, and `S` is a domain. -/
private theorem isTorsionFree : Module.IsTorsionFree R S :=
  .of_smul_eq_zero fun r s hrs ↦ by
    rw [Algebra.smul_def, mul_eq_zero] at hrs
    exact hrs.imp
      (fun h ↦ algebraMap_injective_of_field_isFractionRing R S F F' (by rw [h, map_zero])) id

end Chart

variable [Algebra.IsIntegral F F']

section Restrict

variable (k F) (P' : Place k' F') (hS : ∀ s : S, algebraMap S F' s ∈ P'.integers)

include hS

omit [IsDedekindDomain R] [IsFractionRing R F] [IsDedekindDomain S] [IsFractionRing S F'] in
/-- **The restriction of a place finite on `S` is finite on `R`**: an element of `R`, viewed in
`F'`, may equally be read along `R → S`. -/
theorem algebraMap_mem_integers_restrict (r : R) :
    algebraMap R F r ∈ (P'.restrict k F).integers := by
  rw [mem_integers_restrict_iff, ← IsScalarTower.algebraMap_apply R F F',
    IsScalarTower.algebraMap_apply R S F']
  exact hS _

omit hS [IsDedekindDomain R] [IsFractionRing R F] [IsDedekindDomain S] [IsFractionRing S F'] in
/-- A function of `F` has a zero at a place of `F'` exactly when it has a zero at the restriction
of that place, because the ramification index is a positive factor. -/
private theorem ord_algebraMap_pos_iff (x : F) :
    0 < P'.ord (algebraMap F F' x) ↔ 0 < (P'.restrict k F).ord x := by
  have he : (0 : ℤ) < ramificationIdx F P' := mod_cast ramificationIdx_pos F P'
  rw [ord_algebraMap_restrict k F P' x]
  exact mul_pos_iff_of_pos_left he

/-- **The centre on `S` of a place of `F' / k'` finite on `S` lies over the centre on `R` of its
restriction to `F`** (Stichtenoth, Proposition 3.1.4 at the level of the models): a function of `R`
vanishes at the restriction exactly when its image in `S` vanishes at the place. -/
theorem center_liesOver :
    (P'.center hS).asIdeal.LiesOver
      ((P'.restrict k F).center (R := R) (algebraMap_mem_integers_restrict k F P' hS)).asIdeal where
  over := by
    refine Ideal.ext fun r ↦ ?_
    rcases eq_or_ne r 0 with rfl | hr
    · simp
    have hr' : algebraMap R S r ≠ 0 :=
      fun h ↦ hr (algebraMap_injective_of_field_isFractionRing R S F F' (by rw [h, map_zero]))
    rw [Ideal.mem_under, mem_center_asIdeal_iff_ord_pos _ _ hr,
      mem_center_asIdeal_iff_ord_pos _ _ hr', ← IsScalarTower.algebraMap_apply R S F',
      IsScalarTower.algebraMap_apply R F F', ord_algebraMap_pos_iff k F P']

include k in
/-- **The ramification index of a place over its restriction is the ramification index of the
centres** (Stichtenoth, Definition 3.1.5): both measure how the adic valuation of the centre on `S`
scales the adic valuation of the centre on `R`. The base field `k` does not appear in the
statement — `TauCeti.Place.ramificationIdx` does not depend on it — but it is what names the
place of `F / k` that `P'` lies over. -/
theorem ramificationIdx_eq_ramificationIdx_center :
    ramificationIdx F P' = (P'.center hS).asIdeal.ramificationIdx R := by
  have := isTorsionFree (F := F) (F' := F') (R := R) (S := S)
  have := center_liesOver (R := R) k F P' hS
  set hR := algebraMap_mem_integers_restrict (R := R) k F P' hS
  set 𝔭 := (P'.restrict k F).center hR
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx 𝔭.asIdeal _ 𝔭.ne_bot]
  refine ramificationIdx_eq_of_forall_ord_eq k F P' fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : algebraMap F F' x ≠ 0 := by simpa using hx
  have key := HeightOneSpectrum.valuation_liesOver F' 𝔭 (P'.center hS) x
  rw [(P'.restrict k F).valuation_center hR, P'.valuation_center hS,
    (P'.restrict k F).valuation_eq_exp_neg_ord hx, ← WithZero.exp_nsmul, nsmul_eq_mul] at key
  rw [P'.ord_eq_iff_valuation_eq_exp_neg hx', ← key]
  ring_nf

section ResidueDegree

variable [Algebra k R] [IsScalarTower k R F] [Algebra k' S] [IsScalarTower k' S F']

/-- **The relative degree of a place over its restriction is the residue degree of the centres**
(Stichtenoth, Definition 3.1.5): the residue field of a place finite on a model is the model modulo
the centre of the place, and the two identifications are compatible with `R → S`. -/
theorem relativeDegree_eq_inertiaDeg_center :
    relativeDegree k F P' = (P'.center hS).asIdeal.inertiaDeg R := by
  have := center_liesOver (R := R) k F P' hS
  set hR := algebraMap_mem_integers_restrict (R := R) k F P' hS
  rw [Ideal.inertiaDeg_eq_of_isMaximal ((P'.restrict k F).center hR).asIdeal
    (P'.center hS).asIdeal, relativeDegree_def]
  refine (Algebra.finrank_eq_of_equiv_equiv
    ((P'.restrict k F).quotientAlgEquivResidueField hR).toRingEquiv
    (P'.quotientAlgEquivResidueField hS).toRingEquiv ?_).symm
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_ringEquiv, Ideal.Quotient.algebraMap_mk_of_liesOver,
    quotientAlgEquivResidueField_mk, residueHom_apply,
    IsLocalRing.ResidueField.algebraMap_residue]
  refine congrArg _ (Subtype.ext ?_)
  rw [coe_algebraMap_integers, ← IsScalarTower.algebraMap_apply R F F',
    IsScalarTower.algebraMap_apply R S F']

end ResidueDegree

end Restrict

section OfPrime

variable [Algebra k R] [IsScalarTower k R F] [Algebra k' S] [IsScalarTower k' S F']
variable (k F) (𝔭 : HeightOneSpectrum R)

include k in
/-- **A place of `F' / k'` lies over the place of a height one prime of `R` as soon as the
corresponding prime of `S` lies over it.** -/
theorem restrict_ofPrime (𝔓 : HeightOneSpectrum S) [𝔓.asIdeal.LiesOver 𝔭.asIdeal] :
    (ofPrime k' F' 𝔓).restrict k F = ofPrime k F 𝔭 := by
  have hS := algebraMap_mem_integers_ofPrime k' F' 𝔓
  have hlies := center_liesOver (R := R) k F (ofPrime k' F' 𝔓) hS
  rw [center_ofPrime] at hlies
  have h𝔭 : ((ofPrime k' F' 𝔓).restrict k F).center
      (algebraMap_mem_integers_restrict (R := R) k F (ofPrime k' F' 𝔓) hS) = 𝔭 :=
    HeightOneSpectrum.ext (hlies.over.trans (Ideal.over_def 𝔓.asIdeal 𝔭.asIdeal).symm)
  rw [← h𝔭, ofPrime_center]

include k in
omit [Algebra k R] [IsScalarTower k R F] in
/-- **The ramification index over `F` of the place of a height one prime `𝔓` of `S` is the
ramification index of `𝔓` over `R`.** -/
theorem ramificationIdx_ofPrime (𝔓 : HeightOneSpectrum S) :
    ramificationIdx F (ofPrime k' F' 𝔓) = 𝔓.asIdeal.ramificationIdx R := by
  rw [ramificationIdx_eq_ramificationIdx_center (R := R) k F (ofPrime k' F' 𝔓)
    (algebraMap_mem_integers_ofPrime k' F' 𝔓), center_ofPrime]

/-- **The relative degree over `F` of the place of a height one prime `𝔓` of `S` is the residue
degree of `𝔓` over `R`.** -/
theorem relativeDegree_ofPrime (𝔓 : HeightOneSpectrum S) :
    relativeDegree k F (ofPrime k' F' 𝔓) = 𝔓.asIdeal.inertiaDeg R := by
  rw [relativeDegree_eq_inertiaDeg_center (R := R) k F (ofPrime k' F' 𝔓)
    (algebraMap_mem_integers_ofPrime k' F' 𝔓), center_ofPrime]

variable [Module.Finite R S]

omit [IsDedekindDomain S] [IsFractionRing S F'] [Algebra k' S] [IsScalarTower k' S F'] in
/-- A place of `F' / k'` lying over the place of a height one prime of `R` is finite on `S`: it is
finite on `R`, and `S` is integral over `R`. -/
theorem algebraMap_mem_integers_of_restrict_eq_ofPrime {P' : Place k' F'}
    (h : P'.restrict k F = ofPrime k F 𝔭) (s : S) : algebraMap S F' s ∈ P'.integers := by
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  refine P'.mem_integers_of_isIntegral (R := R) (fun r ↦ ?_)
    ((Algebra.IsIntegral.isIntegral (R := R) s).map (IsScalarTower.toAlgHom R S F'))
  rw [IsScalarTower.algebraMap_apply R F F', ← mem_integers_restrict_iff k F P', h]
  exact algebraMap_mem_integers_ofPrime k F 𝔭 r

omit [IsDedekindDomain S] [IsFractionRing S F'] [Algebra k' S] [IsScalarTower k' S F'] in
/-- The centre on `R` of a place of `F' / k'` restricting to the place of `𝔭` is `𝔭`. -/
private theorem center_restrict_eq {P' : Place k' F'} (h : P'.restrict k F = ofPrime k F 𝔭) :
    (P'.restrict k F).center (algebraMap_mem_integers_restrict (R := R) k F P'
      (algebraMap_mem_integers_of_restrict_eq_ofPrime (S := S) k F 𝔭 h)) = 𝔭 :=
  ((P'.restrict k F).eq_center _ (by rw [h, valuation_ofPrime])).symm

omit [Algebra k' S] [IsScalarTower k' S F'] in
/-- The centre on `S` of a place of `F' / k'` restricting to the place of `𝔭` lies over `𝔭`. -/
private theorem center_liesOver_of_restrict_eq_ofPrime {P' : Place k' F'}
    (h : P'.restrict k F = ofPrime k F 𝔭) :
    (P'.center (algebraMap_mem_integers_of_restrict_eq_ofPrime (S := S) k F 𝔭 h)).asIdeal.LiesOver
      𝔭.asIdeal := by
  have hlies := center_liesOver (R := R) k F P'
    (algebraMap_mem_integers_of_restrict_eq_ofPrime (S := S) k F 𝔭 h)
  rwa [center_restrict_eq (S := S) k F 𝔭 h] at hlies

/-- **The places of `F' / k'` lying over the place of a height one prime `𝔭` of `R` are exactly
the primes of `S` lying over `𝔭`** (Stichtenoth, Section III.2): a place over the place of `𝔭` is
finite on `S`, and its centre is a prime over `𝔭`. -/
noncomputable def restrictOfPrimeEquivPrimesOver :
    {P' : Place k' F' // P'.restrict k F = ofPrime k F 𝔭} ≃ 𝔭.asIdeal.primesOver S :=
  have := FaithfulSMul.of_field_isFractionRing R S F F'
  { toFun P' :=
      ⟨(P'.1.center (algebraMap_mem_integers_of_restrict_eq_ofPrime (S := S) k F 𝔭 P'.2)).asIdeal,
        inferInstance, center_liesOver_of_restrict_eq_ofPrime k F 𝔭 P'.2⟩
    invFun 𝔓 :=
      ⟨ofPrime k' F' ⟨𝔓.1, 𝔓.2.1, Ideal.ne_bot_of_mem_primesOver (A := R) 𝔭.ne_bot 𝔓.2⟩,
        have := 𝔓.2.2
        restrict_ofPrime k F 𝔭 _⟩
    left_inv P' := Subtype.ext (ofPrime_center k' F' P'.1 _)
    right_inv _𝔓 := Subtype.ext (congrArg HeightOneSpectrum.asIdeal (center_ofPrime k' F' _)) }

@[simp]
theorem restrictOfPrimeEquivPrimesOver_apply_coe
    (P' : {P' : Place k' F' // P'.restrict k F = ofPrime k F 𝔭}) :
    (restrictOfPrimeEquivPrimesOver k F 𝔭 P').1 =
      (P'.1.center (algebraMap_mem_integers_of_restrict_eq_ofPrime (S := S) k F 𝔭 P'.2)).asIdeal :=
  (rfl)

@[simp]
theorem restrictOfPrimeEquivPrimesOver_symm_apply_coe (𝔓 : HeightOneSpectrum S)
    (h𝔓 : 𝔓.asIdeal ∈ 𝔭.asIdeal.primesOver S) :
    ((restrictOfPrimeEquivPrimesOver k F 𝔭).symm ⟨𝔓.asIdeal, h𝔓⟩).1 = ofPrime k' F' 𝔓 :=
  (rfl)

section Sum

variable (S)

include S in
/-- **The fundamental identity** (Stichtenoth, Theorem 3.1.11) at a place of the finite chart of a
model: the ramification indices and relative degrees of the places of `F' / k'` lying over the
place of a height one prime `𝔭` of `R` satisfy `∑ e(P' ∣ P) · f(P' ∣ P) = [F' : F]`. Together with
`TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_le_finrank` this settles the fibre over every
place that lies on some affine model. -/
theorem sum_ramificationIdx_mul_relativeDegree_eq_finrank {s : Finset (Place k' F')}
    (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = ofPrime k F 𝔭) :
    ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P' = Module.finrank F F' := by
  have := isTorsionFree (F := F) (F' := F') (R := R) (S := S)
  have : Fintype (𝔭.asIdeal.primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver (S := S) 𝔭.asIdeal).fintype
  have key : ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P'
      = ∑ 𝔓 : 𝔭.asIdeal.primesOver S, 𝔓.1.ramificationIdx R * 𝔓.1.inertiaDeg R := by
    rw [← Finset.sum_coe_sort s fun P' ↦ ramificationIdx F P' * relativeDegree k F P']
    refine Fintype.sum_equiv
      ((Equiv.subtypeEquivRight hs).trans (restrictOfPrimeEquivPrimesOver k F 𝔭)) _ _ fun P' ↦ ?_
    have hSint := algebraMap_mem_integers_of_restrict_eq_ofPrime (S := S) k F 𝔭 ((hs P'.1).mp P'.2)
    rw [ramificationIdx_eq_ramificationIdx_center (R := R) k F P'.1 hSint,
      relativeDegree_eq_inertiaDeg_center (R := R) k F P'.1 hSint]
    simp
  rw [key, Ideal.sum_ramification_inertia_eq_finrank 𝔭.asIdeal S]
  exact (IsFractionRing.finrank_eq R F S F').symm

end Sum

end OfPrime

end Place

end TauCeti
