/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Scheme
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Basic

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

* `TauCeti.SlStd.kostantRootSubgroupMatrix_eq_transvection`: the represented type-A root
  subgroups are the standard elementary transvections.
* `TauCeti.SlStd.specialLinearDefiningHopfIdeal_le_kostantToralDefiningIdeal`: the
  determinant-one equation belongs to the carrier's defining Hopf ideal.
* `TauCeti.SlStd.det_eq_one_of_mem_points`: every matrix point of the carrier has determinant one.
* `TauCeti.SlStd.toSpecialLinear`: the canonical closed immersion from the carrier to
  `SL_{r+1}`.
* `TauCeti.SlStd.toSpecialLinear_comp_groupSchemeι`: composing with `SL_{r+1} → GL_{r+1}`
  recovers the carrier inclusion.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: the full-weight type `A` carrier is now proved to lie
in the expected pinned ambient group.  Identifying it with that group remains the generation
step.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

namespace TauCeti.SlStd

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open scoped CategoryTheory.MonObj

attribute [local instance high] Algebra.toModule

variable (r : ℕ)

/-- The represented type-A root subgroup is the elementary transvection from the root source to
the root target. -/
theorem kostantRootSubgroupMatrix_eq_transvection {A : Type*} [CommRing A]
    (k : Fin r ⊕ Fin r)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) :
    TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
        (isNilpotent_rep_rootGenerator r k) (latticeBasis r) q =
      TauCeti.transvectionUnit (rootTarget_ne_rootSource r k)
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q)) := by
  exact
    TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_transvectionUnit_of_action
        (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
        (isNilpotent_rep_rootGenerator r k) (latticeBasis r) (rootSource r k)
        (rootTarget r k) (rootTarget_ne_rootSource r k)
        (nilpotencyClass_rep_rootGenerator r k) (rep_rootGenerator_latticeBasis_apply r k) q

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
  have hpoint : GeneralLinear.pointToGeneralLinear (r + 1)
      (toConv (q.ofConv.comp f.hom.toAlgHom)) = m :=
    TauCeti.UniversalEnvelopingAlgebra.pointsMulEquiv_kostantRootSubgroupCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
      (isNilpotent_rep_rootGenerator r k) (latticeBasis r)
      (AdditiveGroup.coordinateHopfAlgebra ℤ) q
  have hpoint' : GeneralLinear.pointToGeneralLinear (r + 1)
      (toConv f.hom.toAlgHom) = m := by
    simpa only [hq, AlgHom.id_comp, WithConv.ofConv_toConv] using hpoint
  have hmatrix : m = TauCeti.transvectionUnit (rootTarget_ne_rootSource r k)
      (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv q)) :=
    kostantRootSubgroupMatrix_eq_transvection r k q
  calc
    f.hom (GeneralLinear.determinantGroupLike ℤ (r + 1) :
        GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) =
        Matrix.det (GeneralLinear.pointToGeneralLinear (r + 1)
          (toConv f.hom.toAlgHom)).val := by
      simpa only [WithConv.ofConv_toConv, BialgHom.coe_toAlgHom] using
        (GeneralLinear.point_apply_determinantGroupLike (R := ℤ) (n := r + 1)
          (toConv f.hom.toAlgHom))
    _ = Matrix.det m.val := congrArg (fun g => Matrix.det g.val) hpoint'
    _ = 1 := by
      rw [hmatrix, ← Matrix.GeneralLinearGroup.val_det_apply,
        TauCeti.det_transvectionUnit, Units.val_one]

/-- **The determinant-one equation belongs to the defining Hopf ideal of the full-weight type
`A_r` carrier.** Equivalently, every represented root subgroup and the represented weight torus
factor through `SL_{r+1}`. -/
theorem specialLinearDefiningHopfIdeal_le_kostantToralDefiningIdeal :
    SpecialLinear.definingHopfIdeal ℤ (r + 1) ≤
      TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) := by
  rw [TauCeti.UniversalEnvelopingAlgebra.le_kostantToralDefiningIdeal_iff]
  constructor
  · intro k
    exact SpecialLinear.definingHopfIdeal_toIdeal_le_ker_of_map_determinant_eq_one ℤ (r + 1) _
      (rootCoordinateMap_determinantGroupLike r k)
  · exact SpecialLinear.definingHopfIdeal_toIdeal_le_ker_of_map_determinant_eq_one ℤ (r + 1) _
      (GeneralLinear.weightTorusCoordinateMap_determinantGroupLike (R := ℤ) (weight r)
        (sum_weight_eq_zero r))

/-- Every matrix-valued point of the full-weight type `A_r` carrier has determinant one. -/
theorem det_eq_one_of_mem_points {A : Type*} [CommRing A]
    {g : Matrix.GeneralLinearGroup (Fin (r + 1)) A} (hg : g ∈ points r A) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  let p := (GeneralLinear.pointsMulEquiv (R := ℤ) (r + 1)).symm g
  have hspecial_toIdeal :
      (GeneralLinear.determinantGroupLike ℤ (r + 1) :
          GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) - 1 ∈
        (SpecialLinear.definingHopfIdeal ℤ (r + 1)).toIdeal := by
    rw [SpecialLinear.definingHopfIdeal_toIdeal]
    exact Ideal.mem_span_singleton_self _
  have hspecial :
      (GeneralLinear.determinantGroupLike ℤ (r + 1) :
          GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) - 1 ∈
        SpecialLinear.definingHopfIdeal ℤ (r + 1) :=
    HopfIdeal.mem_toIdeal.mpr hspecial_toIdeal
  have hzero := (mem_points_iff r A g).mp hg _
    (specialLinearDefiningHopfIdeal_le_kostantToralDefiningIdeal r hspecial)
  have hpdet : p.ofConv
      (GeneralLinear.determinantGroupLike ℤ (r + 1) :
        GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) = 1 := by
    simpa only [map_sub, map_one, sub_eq_zero] using hzero
  apply Units.ext
  rw [Units.val_one, Matrix.GeneralLinearGroup.val_det_apply]
  calc
    Matrix.det g.val =
        Matrix.det (GeneralLinear.pointToGeneralLinear (r + 1) p).val := by
      rw [← GeneralLinear.pointsMulEquiv_apply]
      dsimp only [p]
      rw [MulEquiv.apply_symm_apply]
    _ = p.ofConv
        (GeneralLinear.determinantGroupLike ℤ (r + 1) :
          GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) :=
      (GeneralLinear.point_apply_determinantGroupLike ℤ (r + 1) p).symm
    _ = 1 := hpdet

/-- The canonical morphism from the full-weight type `A_r` carrier to `SL_{r+1}`, induced by the
containment of defining Hopf ideals. -/
noncomputable def toSpecialLinear : groupScheme r ⟶ SpecialLinear.groupScheme ℤ (r + 1) :=
  CommHopfAlgCat.quotientSpecMapOfLe
      (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
      (specialLinearDefiningHopfIdeal_le_kostantToralDefiningIdeal r) ≫
    eqToHom (SpecialLinear.groupScheme_def ℤ (r + 1)).symm

/-- The canonical morphism from the type `A_r` carrier to `SL_{r+1}` is a closed immersion. -/
instance isClosedImmersion_toSpecialLinear :
    IsClosedImmersion (toSpecialLinear r).hom.hom.left := by
  rw [toSpecialLinear, CommHopfAlgCat.quotientSpecMapOfLe_def]
  apply (CommHopfAlgCat.isClosedImmersion_hopfSpec_map_comp_eqToHom_iff
    (SpecialLinear.groupScheme_def ℤ (r + 1))
    (CommHopfAlgCat.quotientMapOfLe (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
      (specialLinearDefiningHopfIdeal_le_kostantToralDefiningIdeal r))).2
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
