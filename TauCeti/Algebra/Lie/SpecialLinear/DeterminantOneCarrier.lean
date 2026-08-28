/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Scheme
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# The type A full-weight carrier has determinant one

The standard Chevalley generators of `sl_{r+1}` act as matrix units, so their divided-power
exponentials are transvections.  The product of the weights of the standard representation is the
trivial character.  Consequently every generator used to define `TauCeti.SlStd.groupScheme r`
has determinant one, and the carrier is a closed subgroup scheme of `SL_{r+1}`.

This is the determinant-one half of identifying the full-weight type `A_r` carrier with the
special linear group scheme.  The reverse inclusion, which requires a generation theorem, is not
asserted here.

## Main declarations

* `TauCeti.SlStd.definingHopfIdeal_le_carrierDefiningHopfIdeal`: the determinant-one equation
  belongs to the carrier's defining Hopf ideal.
* `TauCeti.SlStd.toSpecialLinear`: the canonical closed immersion from the carrier to
  `SL_{r+1}`.
* `TauCeti.SlStd.toSpecialLinear_comp_groupSchemeι`: composing with `SL_{r+1} → GL_{r+1}`
  recovers the carrier inclusion.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: the full-weight type `A` carrier is now proved to lie
in the expected pinned ambient group.  Identifying it with that group remains the generation
step.
-/

public section

namespace TauCeti.SlStd

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open scoped CategoryTheory.MonObj

attribute [local instance high] Algebra.toModule

variable (r : ℕ)

private theorem nilpotencyClass_rep_rootGenerator (k : Fin r ⊕ Fin r) :
    nilpotencyClass
        (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k))) = 2 := by
  refine nilpotencyClass_eq_succ_iff.mpr ⟨pow_two_rep_rootGenerator_eq_zero r k, ?_⟩
  rw [pow_one]
  intro hzero
  have h := DFunLike.congr_fun hzero (Pi.single (rootSource r k) 1)
  rw [rep_rootGenerator_single_source] at h
  have := congrFun h (rootTarget r k)
  simp at this

private theorem rep_rootGenerator_latticeBasis_apply (k : Fin r ⊕ Fin r)
    (s : Fin (r + 1)) :
    rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k))
        ((latticeBasis r s : (lattice r).toAddSubgroup) : Fin (r + 1) → ℚ) =
      if s = rootSource r k then
        ((latticeBasis r (rootTarget r k) : (lattice r).toAddSubgroup) : Fin (r + 1) → ℚ)
      else 0 := by
  rw [coe_latticeBasis, rep_rootGenerator_apply]
  split_ifs with hs
  · subst hs
    rw [Pi.single_eq_same, one_smul, coe_latticeBasis]
  · simp [hs]

private theorem integralDividedPower_one_rootGenerator (k : Fin r ⊕ Fin r)
    (s : Fin (r + 1)) :
    integralDividedPower
        (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r k)))
        (lattice r).toAddSubgroup 1
        (fun _ hv =>
          TauCeti.UniversalEnvelopingAlgebra.dividedPower_apply_mem_of_kostantForm_apply_mem
            (rootGenerator r) (cartanGenerator r) (rep r)
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k 1 hv)
        (latticeBasis r s) =
      if s = rootSource r k then latticeBasis r (rootTarget r k) else 0 := by
  apply Subtype.ext
  rw [coe_integralDividedPower_apply,
    Associative.dividedPower_one, Module.End.smul_def,
    rep_rootGenerator_latticeBasis_apply]
  split_ifs <;> rfl

private theorem kostantRootSubgroupPoints_apply_latticeBasis {A : Type*} [CommRing A]
    (k : Fin r ⊕ Fin r)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) (s : Fin (r + 1)) :
    (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
        (isNilpotent_rep_rootGenerator r k) q).val ((latticeBasis r).baseChange A s) =
      (latticeBasis r).baseChange A s +
        if s = rootSource r k then
          Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q) •
            (latticeBasis r).baseChange A (rootTarget r k)
        else 0 := by
  rw [Module.Basis.baseChange_apply,
    TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_tmul,
    nilpotencyClass_rep_rootGenerator, Finset.sum_range_succ, Finset.sum_range_one,
    integralDividedPower_zero,
    integralDividedPower_one_rootGenerator]
  split_ifs <;> simp [smul_tmul']

private theorem kostantRootSubgroupMatrix_eq_transvection {A : Type*} [CommRing A]
    (k : Fin r ⊕ Fin r)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) :
    TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
        (isNilpotent_rep_rootGenerator r k) (latticeBasis r) q =
      TauCeti.transvectionUnit (rootTarget_ne_rootSource r k)
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_apply,
    kostantRootSubgroupPoints_apply_latticeBasis, TauCeti.coe_transvectionUnit]
  simp only [map_add, Module.Basis.repr_self, Finsupp.add_apply, Matrix.transvection,
    Matrix.add_apply, Matrix.one_apply]
  simp only [Matrix.single_apply]
  split_ifs <;> simp_all [rootTarget_ne_rootSource]

private theorem sum_weight_eq_zero : ∑ k, weight r k = 0 := by
  funext i
  simp [weight_apply]

private theorem prod_torusCharacter_weight_eq_one {A : Type*} [CommRing A]
    (s : Fin r → Aˣ) :
    ∏ k, TauCeti.torusCharacter s (weight r k) = 1 := by
  rw [← TauCeti.torusCharacter_zero s, ← sum_weight_eq_zero r]
  induction (Finset.univ : Finset (Fin (r + 1))) using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, TauCeti.torusCharacter_add, ih]

private theorem definingHopfIdeal_toIdeal_le_ker_of_map_determinant_eq_one
    {H : Type} [CommRing H] [HopfAlgebra ℤ H]
    (f : GeneralLinear.coordinateHopfAlgebra ℤ (r + 1) ⟶
      _root_.CommHopfAlgCat.of ℤ H)
    (hdet : f.hom (GeneralLinear.determinantGroupLike ℤ (r + 1) :
      GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) = 1) :
    (SpecialLinear.definingHopfIdeal ℤ (r + 1)).toIdeal ≤
      RingHom.ker f.hom.toAlgHom.toRingHom := by
  rw [SpecialLinear.definingHopfIdeal_toIdeal, Ideal.span_singleton_le_iff_mem,
    RingHom.mem_ker, map_sub]
  change f.hom _ - f.hom 1 = 0
  rw [hdet, map_one, sub_self]

private theorem rootCoordinateMap_determinantGroupLike (k : Fin r ⊕ Fin r) :
    (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
        (isNilpotent_rep_rootGenerator r k) (latticeBasis r)).hom
      (GeneralLinear.determinantGroupLike ℤ (r + 1) :
        GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) = 1 := by
  let f := TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap
    (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
    (isNilpotent_rep_rootGenerator r k) (latticeBasis r)
  let q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ]
      AdditiveGroup.coordinateHopfAlgebra ℤ) :=
    toConv (AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))
  have hq : q.ofConv = AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) :=
    WithConv.ofConv_toConv _
  let m := TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
    (isNilpotent_rep_rootGenerator r k) (latticeBasis r) q
  have hdet := GeneralLinear.point_apply_determinantGroupLike
    (R := ℤ) (n := r + 1) (toConv (q.ofConv.comp f.hom.toAlgHom))
  have hpoint : GeneralLinear.pointToGeneralLinear (r + 1)
      (toConv (q.ofConv.comp f.hom.toAlgHom)) = m :=
    TauCeti.UniversalEnvelopingAlgebra.pointsMulEquiv_kostantRootSubgroupCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
      (isNilpotent_rep_rootGenerator r k) (latticeBasis r)
      (AdditiveGroup.coordinateHopfAlgebra ℤ) q
  have hmatrix : m = TauCeti.transvectionUnit (rootTarget_ne_rootSource r k)
      (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q)) :=
    kostantRootSubgroupMatrix_eq_transvection r k q
  calc
    f.hom (GeneralLinear.determinantGroupLike ℤ (r + 1) :
        GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) =
        Matrix.det (GeneralLinear.pointToGeneralLinear (r + 1)
          (toConv (q.ofConv.comp f.hom.toAlgHom))).val := by
            rw [← hdet, hq, AlgHom.id_comp, WithConv.ofConv_toConv]
            rfl
    _ = Matrix.det m.val := congrArg (fun g => Matrix.det g.val) hpoint
    _ = 1 := by
      rw [hmatrix, ← Matrix.GeneralLinearGroup.val_det_apply,
        TauCeti.det_transvectionUnit, Units.val_one]

private theorem weightTorusCoordinateMap_determinantGroupLike :
    (GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r)).hom
      (GeneralLinear.determinantGroupLike ℤ (r + 1) :
        GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) = 1 := by
  let f := GeneralLinear.weightTorusCoordinateMap (R := ℤ) (weight r)
  let q : WithConv
      ((DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin r))).obj →ₐ[ℤ]
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin r))).obj) :=
    toConv (AlgHom.id ℤ
      (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin r))).obj)
  have hq : q.ofConv = AlgHom.id ℤ
      (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin r))).obj :=
    WithConv.ofConv_toConv _
  let A := CommAlgCat.of ℤ
    (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin r))).obj
  let p : WithConv
      (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1) →ₐ[ℤ]
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup (Fin r))).obj) :=
    (CommHopfAlgCat.mapPointsFunctor f).app A q
  have hdet := GeneralLinear.point_apply_determinantGroupLike
    (R := ℤ) (n := r + 1) p
  have hpoint : GeneralLinear.pointToGeneralLinear (r + 1) p =
      TauCeti.diagGL fun i =>
        TauCeti.torusCharacter (SplitTorus.pointsMulEquiv q) (weight r i) := by
    calc
      GeneralLinear.pointToGeneralLinear (r + 1) p =
          GeneralLinear.pointsMulEquiv (r + 1) p :=
        (GeneralLinear.pointsMulEquiv_apply (r + 1) p).symm
      _ = _ := by
        simpa only [p, f] using
          (GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap
            (R := ℤ) (N := r + 1) (κ := Fin r) (weight r) A q)
  calc
    f.hom (GeneralLinear.determinantGroupLike ℤ (r + 1) :
        GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) =
        Matrix.det (GeneralLinear.pointToGeneralLinear (r + 1) p).val := by
          rw [← hdet]
          dsimp only [p]
          rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply, hq, AlgHom.id_apply]
    _ = Matrix.det (TauCeti.diagGL fun i =>
        TauCeti.torusCharacter (SplitTorus.pointsMulEquiv q) (weight r i)).val := by
          exact congrArg (fun g => Matrix.det g.val) hpoint
    _ = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, TauCeti.det_diagGL,
        prod_torusCharacter_weight_eq_one, Units.val_one]

/-- **The determinant-one equation belongs to the defining Hopf ideal of the full-weight type
`A_r` carrier.** Equivalently, every represented root subgroup and the represented weight torus
factor through `SL_{r+1}`. -/
theorem definingHopfIdeal_le_carrierDefiningHopfIdeal :
    SpecialLinear.definingHopfIdeal ℤ (r + 1) ≤
      TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) := by
  rw [TauCeti.UniversalEnvelopingAlgebra.le_kostantToralDefiningIdeal_iff]
  constructor
  · intro k
    exact definingHopfIdeal_toIdeal_le_ker_of_map_determinant_eq_one r _
      (rootCoordinateMap_determinantGroupLike r k)
  · exact definingHopfIdeal_toIdeal_le_ker_of_map_determinant_eq_one r _
      (weightTorusCoordinateMap_determinantGroupLike r)

/-- The canonical morphism from the full-weight type `A_r` carrier to `SL_{r+1}`, induced by the
containment of defining Hopf ideals. -/
noncomputable def toSpecialLinear : groupScheme r ⟶ SpecialLinear.groupScheme ℤ (r + 1) :=
  CommHopfAlgCat.quotientSpecMapOfLe
      (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
      (definingHopfIdeal_le_carrierDefiningHopfIdeal r) ≫
    eqToHom (SpecialLinear.groupScheme_def ℤ (r + 1)).symm

/-- The canonical morphism from the type `A_r` carrier to `SL_{r+1}` is a closed immersion. -/
instance isClosedImmersion_toSpecialLinear :
    IsClosedImmersion (toSpecialLinear r).hom.hom.left := by
  rw [toSpecialLinear, CommHopfAlgCat.quotientSpecMapOfLe_def]
  apply (CommHopfAlgCat.isClosedImmersion_hopfSpec_map_comp_eqToHom_iff
    (SpecialLinear.groupScheme_def ℤ (r + 1))
    (CommHopfAlgCat.quotientMapOfLe (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
      (definingHopfIdeal_le_carrierDefiningHopfIdeal r))).2
  exact CommHopfAlgCat.quotientMapOfLe_surjective _ _

/-- Including the type `A_r` carrier into `SL_{r+1}` and then into `GL_{r+1}` recovers its
original ambient closed immersion. -/
@[simp]
theorem toSpecialLinear_comp_groupSchemeι :
    toSpecialLinear r ≫ SpecialLinear.groupSchemeι ℤ (r + 1) = carrierι r := by
  rw [toSpecialLinear, SpecialLinear.groupSchemeι_def, carrierι_def,
    TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι_def,
    CommHopfAlgCat.kernelSpecι_def]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc]
  rw [CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι]

end TauCeti.SlStd
