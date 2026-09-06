/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.BaseChange
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup

/-!
# Closed generators of the type-E7 minuscule carrier after base change

The integral type-`E₇` minuscule carrier comes with fourteen numbered simple-root subgroups
and a rank-seven weight torus. This file proves that their transported coordinate maps remain
surjective after base change from `ℤ` to an arbitrary commutative ring. Contravariantly, the
transported root subgroups and weight torus are closed immersions into the specialized carrier.

The resulting morphisms are the scheme-theoretic base changes of the integral pinning generators,
not newly chosen subgroups in each fibre. No assertion is made that the carrier is smooth,
reductive, or geometrically connected, nor that its weight torus is maximal.

## Main declarations

* `TauCeti.E7Minuscule.rootSubgroupToBaseChangeCoordinateMap_surjective`: every transported
  numbered root-subgroup coordinate map is surjective.
* `TauCeti.E7Minuscule.weightTorusToBaseChangeCoordinateMap_surjective`: the transported
  weight-torus coordinate map is surjective.
* `TauCeti.E7Minuscule.baseChangeRootSubgroup` and
  `TauCeti.E7Minuscule.baseChangeWeightTorus`: the corresponding morphisms into the specialized
  carrier.
* `TauCeti.E7Minuscule.baseChangeRootSubgroupClosedSubgroup`: each numbered root subgroup as a
  bundled closed subgroup scheme.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.2.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.DynkinType

namespace TauCeti.E7Minuscule

universe u

noncomputable section

variable (A : Type u) [CommRing A]

/-! ## Surjectivity of the transported coordinate maps -/

/-- The named integral root-subgroup coordinate map is surjective. -/
private theorem rootSubgroupIntegralCoordinateMap_surjective (k : Fin 7 ⊕ Fin 7) :
    Function.Surjective (rootSubgroupIntegralCoordinateMap k).hom := by
  have hrepresented : Function.Surjective
      (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap
        (TauCeti.serreRootGenerator (CartanMatrix.E 7))
        (TauCeti.serreH ℚ (CartanMatrix.E 7)) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k)
        latticeBasis).hom := by
    rw [← TauCeti.UniversalEnvelopingAlgebra.mkQuotient_comp_kostantRootSubgroupToralCoordinateMap
      (TauCeti.serreRootGenerator (CartanMatrix.E 7))
      (TauCeti.serreH ℚ (CartanMatrix.E 7)) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
      e7MinusculeWeight k]
    exact (rootSubgroupCoordinateMap_surjective k).comp
      (CommHopfAlgCat.mkQuotient_surjective _ _)
  apply Function.Surjective.of_comp
    (g := (CommHopfAlgCat.mkQuotient
      (GeneralLinear.coordinateHopfAlgebra ℤ 56) definingIdeal).hom)
  have hcomp : Function.Surjective
      (CommHopfAlgCat.mkQuotient
          (GeneralLinear.coordinateHopfAlgebra ℤ 56) definingIdeal ≫
        rootSubgroupIntegralCoordinateMap k).hom := by
    rw [mkQuotient_comp_rootSubgroupIntegralCoordinateMap]
    exact hrepresented
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] using hcomp

/-- Composing a surjective integral coordinate map with the canonical source and target
identifications preserves surjectivity after base change. -/
private theorem baseChangeCoordinateMap_surjective
    {H L : _root_.CommHopfAlgCat.{0} ℤ}
    {H' L' : _root_.CommHopfAlgCat.{u} A}
    (eH : H' ≅ CommHopfAlgCat.baseChange (K := A) H)
    (eL : CommHopfAlgCat.baseChange (K := A) L ≅ L')
    (f : H ⟶ L) (hf : Function.Surjective f.hom) :
    Function.Surjective
      (eH.hom ≫ CommHopfAlgCat.baseChangeMap (K := A) f ≫ eL.hom).hom := by
  intro y
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso eL.hom).2 y
  obtain ⟨z, rfl⟩ := CommHopfAlgCat.baseChangeMap_surjective (K := A) f hf x
  obtain ⟨w, rfl⟩ := (ConcreteCategory.bijective_of_isIso eH.hom).2 z
  refine ⟨w, ?_⟩
  simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply]

/-- **Every transported numbered type-`E₇` root-subgroup coordinate map is surjective.**
Thus the simple-root copy of `𝔾ₐ` remains scheme-theoretically closed after arbitrary base
change from `ℤ`. -/
theorem rootSubgroupToBaseChangeCoordinateMap_surjective (k : Fin 7 ⊕ Fin 7) :
    Function.Surjective (rootSubgroupToBaseChangeCoordinateMap A k).hom := by
  rw [← baseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap A k]
  let e := AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ A
  exact baseChangeCoordinateMap_surjective A
    (H := CommHopfAlgCat.quotient
      (GeneralLinear.coordinateHopfAlgebra ℤ 56) definingIdeal)
    (L := AdditiveGroup.coordinateHopfAlgebra ℤ)
    (H' := CommHopfAlgCat.quotient
      (GeneralLinear.coordinateHopfAlgebra A 56) (baseChangeDefiningIdeal A))
    (L' := AdditiveGroup.coordinateHopfAlgebra A)
    (baseChangeCoordinateIso A) e (rootSubgroupIntegralCoordinateMap k)
      (rootSubgroupIntegralCoordinateMap_surjective k)

/-- The named integral weight-torus coordinate map is surjective. -/
private theorem weightTorusIntegralCoordinateMap_surjective :
    Function.Surjective weightTorusIntegralCoordinateMap.hom := by
  apply Function.Surjective.of_comp
    (g := (CommHopfAlgCat.mkQuotient
      (GeneralLinear.coordinateHopfAlgebra ℤ 56) definingIdeal).hom)
  have h := GeneralLinear.weightTorusCoordinateMap_surjective (R := ℤ) e7MinusculeWeight
    span_range_e7MinusculeWeight_eq_top
  rw [← mkQuotient_comp_weightTorusIntegralCoordinateMap] at h
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] using h

/-- **The transported rank-seven weight-torus coordinate map is surjective.** Thus the weight
torus remains a closed split torus in every specialized carrier. -/
theorem weightTorusToBaseChangeCoordinateMap_surjective :
    Function.Surjective (weightTorusToBaseChangeCoordinateMap A).hom := by
  rw [← baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap A]
  let e : CommHopfAlgCat.baseChange (K := A)
      ((DiagonalizableGroup.coordinateRing ℤ
        (SplitTorus.characterGroup (Fin 7))).obj) ≅
        (DiagonalizableGroup.coordinateRing A
          (SplitTorus.characterGroup (Fin 7))).obj :=
    _root_.CommHopfAlgCat.isoMk
      (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
        (G := SplitTorus.characterGroup (Fin 7)))
  exact baseChangeCoordinateMap_surjective A
    (H := CommHopfAlgCat.quotient
      (GeneralLinear.coordinateHopfAlgebra ℤ 56) definingIdeal)
    (L := (DiagonalizableGroup.coordinateRing ℤ
      (SplitTorus.characterGroup (Fin 7))).obj)
    (H' := CommHopfAlgCat.quotient
      (GeneralLinear.coordinateHopfAlgebra A 56) (baseChangeDefiningIdeal A))
    (L' := (DiagonalizableGroup.coordinateRing A
      (SplitTorus.characterGroup (Fin 7))).obj)
    (baseChangeCoordinateIso A) e weightTorusIntegralCoordinateMap
      weightTorusIntegralCoordinateMap_surjective

/-! ## Scheme-theoretic closed generators

The current `hopfSpec` bridge requires the base ring and all coordinate rings to inhabit the
same universe. The concrete pinning uses the finite index types `Fin 7` and `Fin 56`, so its
scheme-level packaging is correspondingly stated in the base universe. -/

end


noncomputable section

variable (A : Type) [CommRing A]

/-- The type-`E₇` minuscule carrier specialized to the commutative ring `A`, in its transported
quotient presentation inside `GL₅₆/A`. -/
noncomputable abbrev baseChangeGroupScheme : Grp (Over (Spec (CommRingCat.of A))) :=
  CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra A 56)
    (baseChangeDefiningIdeal A)

/-- A transported positive or negative numbered simple root subgroup of the specialized
type-`E₇` minuscule carrier. -/
noncomputable def baseChangeRootSubgroup (k : Fin 7 ⊕ Fin 7) :
    AdditiveGroup.groupScheme A ⟶ baseChangeGroupScheme A :=
  eqToHom (AdditiveGroup.groupScheme_def A) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of A)).map
      (rootSubgroupToBaseChangeCoordinateMap A k).op

/-- Every transported numbered simple root subgroup is a closed immersion into the specialized
type-`E₇` minuscule carrier. -/
instance isClosedImmersion_baseChangeRootSubgroup (k : Fin 7 ⊕ Fin 7) :
    IsClosedImmersion (baseChangeRootSubgroup A k).hom.hom.left := by
  rw [baseChangeRootSubgroup]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_iff
    (AdditiveGroup.groupScheme_def A)
    (rootSubgroupToBaseChangeCoordinateMap A k)).2
      (rootSubgroupToBaseChangeCoordinateMap_surjective A k)

/-- A transported numbered simple root subgroup as a closed subgroup scheme of the specialized
type-`E₇` minuscule carrier. -/
noncomputable def baseChangeRootSubgroupClosedSubgroup (k : Fin 7 ⊕ Fin 7) :
    ClosedSubgroupScheme (baseChangeGroupScheme A) :=
  ClosedSubgroupScheme.mk (baseChangeRootSubgroup A k)

/-- The bundled closed root subgroup is represented by the transported root-subgroup morphism. -/
@[simp]
theorem coe_baseChangeRootSubgroupClosedSubgroup (k : Fin 7 ⊕ Fin 7) :
    (baseChangeRootSubgroupClosedSubgroup A k).1 =
      letI := mono_of_isClosedImmersion_underlying (baseChangeRootSubgroup A k)
      Subobject.mk (baseChangeRootSubgroup A k) :=
  ClosedSubgroupScheme.coe_mk _

/-- The bundled transported root subgroup is canonically isomorphic to the additive group
scheme. -/
noncomputable def baseChangeRootSubgroupClosedSubgroupIso (k : Fin 7 ⊕ Fin 7) :
    ((baseChangeRootSubgroupClosedSubgroup A k).1 :
      Grp (Over (Spec (CommRingCat.of A)))) ≅ AdditiveGroup.groupScheme A :=
  ClosedSubgroupScheme.mkIso (baseChangeRootSubgroup A k)

/-- The canonical parametrization of the bundled closed subgroup followed by its inclusion is
the transported root-subgroup map. -/
@[simp]
theorem baseChangeRootSubgroupClosedSubgroupIso_inv_comp_arrow (k : Fin 7 ⊕ Fin 7) :
    (baseChangeRootSubgroupClosedSubgroupIso A k).inv ≫
        (baseChangeRootSubgroupClosedSubgroup A k).1.arrow =
      baseChangeRootSubgroup A k :=
  ClosedSubgroupScheme.mkIso_inv_comp_arrow (baseChangeRootSubgroup A k)

/-- The transported rank-seven weight torus of the specialized type-`E₇` minuscule carrier. -/
noncomputable def baseChangeWeightTorus :
    SplitTorus.groupScheme A (Fin 7) ⟶ baseChangeGroupScheme A :=
  eqToHom (DiagonalizableGroup.groupScheme_def A
      (SplitTorus.characterGroup (Fin 7))) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of A)).map
      (weightTorusToBaseChangeCoordinateMap A).op

/-- The transported weight-torus morphism is a closed immersion into the specialized carrier. -/
instance isClosedImmersion_baseChangeWeightTorus :
    IsClosedImmersion (baseChangeWeightTorus A).hom.hom.left := by
  rw [baseChangeWeightTorus]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_iff
    (DiagonalizableGroup.groupScheme_def A (SplitTorus.characterGroup (Fin 7)))
    (weightTorusToBaseChangeCoordinateMap A)).2
      (weightTorusToBaseChangeCoordinateMap_surjective A)

end

end TauCeti.E7Minuscule
