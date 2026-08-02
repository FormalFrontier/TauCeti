/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.CoordinateHopfAlgebra

/-!
# The general linear group scheme

For a commutative ring `R` and a natural number `n`, the coordinate Hopf algebra of the general
linear group is the determinant localization

`R[Xᵢⱼ][det(X)⁻¹]`.

Applying relative spectrum to the bundled coordinate Hopf algebra gives an affine group scheme
over `Spec R`. This file presents its underlying scheme canonically as the spectrum of the raw
determinant localization. Under that presentation, the structural morphism, unit,
multiplication, and inversion are induced contravariantly by the algebra structure map, counit,
comultiplication, and antipode, respectively. The multiplication source is identified with the
spectrum of the tensor square of the raw coordinate ring.

The construction includes rank zero and the zero ring. Mathlib's current `hopfSpec` construction
requires the base ring and Hopf-algebra carrier to lie in the same universe, so this file uses that
same-universe setting.

## Main declarations

* `TauCeti.GeneralLinear.groupScheme`: the general linear group scheme over `Spec R`.
* `TauCeti.GeneralLinear.groupSchemeSpecIso`: its canonical raw-coordinate presentation.
* `TauCeti.GeneralLinear.groupSchemeMulSourceIso`: the tensor-coordinate presentation of the
  multiplication source.
* `TauCeti.GeneralLinear.groupScheme_one_left`,
  `TauCeti.GeneralLinear.groupScheme_mul_left`, and
  `TauCeti.GeneralLinear.groupScheme_inv_left`: the raw-coordinate formulas for the group
  operations.
* `TauCeti.GeneralLinear.isAffine_groupScheme` and
  `TauCeti.GeneralLinear.locallyOfFiniteType_groupScheme`: affineness and local finite type over
  the base.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter IV, section 1.8.
* The Stacks Project, Tags
  [022W](https://stacks.math.columbia.edu/tag/022W) and
  [00CM](https://stacks.math.columbia.edu/tag/00CM).
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

namespace GeneralLinear

open AlgebraicGeometry MonObj MonoidalCategory

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The general linear group scheme obtained by applying relative spectrum to its coordinate
Hopf algebra.

The same-universe restriction is imposed by Mathlib's current `hopfSpec` construction. -/
noncomputable def groupScheme : Grp (Over (Spec (CommRingCat.of R))) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
    (Opposite.op (coordinateHopfAlgebra R n))

private lemma groupScheme_X_left_bundled :
    (groupScheme R n).X.left =
      Spec (CommRingCat.of (coordinateHopfAlgebra R n)) := by
  unfold groupScheme
  rfl

/-- The scheme underlying the general linear group scheme is canonically isomorphic to the
spectrum of the determinant localization. -/
noncomputable def groupSchemeSpecIso :
    (groupScheme R n).X.left ≅ Spec (CommRingCat.of (CoordinateRing R n)) :=
  eqToIso (groupScheme_X_left_bundled R n) ≪≫
    Scheme.Spec.mapIso
      (coordinateHopfAlgebraAlgEquiv R n).toRingEquiv.toCommRingCatIso.op

private lemma groupScheme_X_hom_bundled :
    (groupScheme R n).X.hom =
      eqToHom (groupScheme_X_left_bundled R n) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (coordinateHopfAlgebra R n))) := by
  simpa only [eqToHom_refl, Category.comp_id] using
    (conj_eqToHom_iff_heq
      (groupScheme R n).X.hom
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (coordinateHopfAlgebra R n))))
      (groupScheme_X_left_bundled R n) rfl).2 (by
        unfold groupScheme
        exact heq_of_eq (AlgebraicGeometry.algSpec_obj_hom
          (R := CommRingCat.of R)
          (Opposite.op (CommAlgCat.of R (coordinateHopfAlgebra R n)))))

/-- The structural morphism of the general linear group scheme is induced by the algebra
structure map on the determinant localization. -/
@[simp]
lemma groupScheme_X_hom :
    (groupScheme R n).X.hom =
      (groupSchemeSpecIso R n).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R n))) := by
  calc
    (groupScheme R n).X.hom =
        eqToHom (groupScheme_X_left_bundled R n) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap R (coordinateHopfAlgebra R n))) :=
      groupScheme_X_hom_bundled R n
    _ = (groupSchemeSpecIso R n).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R n))) := by
      simp only [groupSchemeSpecIso, Iso.trans_hom, eqToIso.hom,
        Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op,
        Category.assoc, ← Spec.map_comp]
      congr 2
      ext r
      exact (coordinateHopfAlgebraAlgEquiv R n).commutes r |>.symm

private noncomputable def coordinateTensorAlgEquiv :
    CoordinateRing R n ⊗[R] CoordinateRing R n ≃ₐ[R]
      coordinateHopfAlgebra R n ⊗[R] coordinateHopfAlgebra R n :=
  Algebra.TensorProduct.congr
    (coordinateHopfAlgebraAlgEquiv R n) (coordinateHopfAlgebraAlgEquiv R n)

private lemma groupScheme_tensor_X_left_bundled :
    ((groupScheme R n).X ⊗ (groupScheme R n).X).left =
      Limits.pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (coordinateHopfAlgebra R n))))
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (coordinateHopfAlgebra R n)))) := by
  rw [Over.tensorObj_left]
  have h : (groupScheme R n).X.hom ≍
      Spec.map (CommRingCat.ofHom
        (algebraMap R (coordinateHopfAlgebra R n))) := by
    rw [groupScheme_X_hom_bundled]
    exact eqToHom_comp_heq _ _
  cases groupScheme_X_left_bundled R n
  exact congrArg (fun k ↦ Limits.pullback k k) (eq_of_heq h)

/-- The multiplication source is canonically the spectrum of the tensor square of the raw
determinant-localization coordinate ring. This combines the fibre-product presentation of the
product over `Spec R`, the standard affine pullback isomorphism, and the coordinate equivalence on
both tensor factors. -/
noncomputable def groupSchemeMulSourceIso :
    ((groupScheme R n).X ⊗ (groupScheme R n).X).left ≅
      Spec (CommRingCat.of (CoordinateRing R n ⊗[R] CoordinateRing R n)) :=
  eqToIso (groupScheme_tensor_X_left_bundled R n) ≪≫
    pullbackSpecIso R (coordinateHopfAlgebra R n) (coordinateHopfAlgebra R n) ≪≫
    Scheme.Spec.mapIso (coordinateTensorAlgEquiv R n).toRingEquiv.toCommRingCatIso.op

private lemma algSpec_map_left_ofAlgHom {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    ((AlgebraicGeometry.algSpec (CommRingCat.of R)).map
      (CommAlgCat.ofHom f).op).left =
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [AlgebraicGeometry.algSpec_map_left]
  rfl

private lemma groupScheme_eq_asOver :
    groupScheme R n =
      Grp.mk ((Spec (CommRingCat.of (coordinateHopfAlgebra R n))).asOver
        (Spec (CommRingCat.of R))) :=
  rfl

private lemma groupScheme_one_left_bundled :
    η[(groupScheme R n).X].left =
      Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom R (coordinateHopfAlgebra R n))) ≫
      eqToHom (groupScheme_X_left_bundled R n).symm := by
  simpa only [eqToHom_refl, Category.id_comp] using
    (conj_eqToHom_iff_heq
      η[(groupScheme R n).X].left
      (Spec.map (CommRingCat.ofHom
        (Bialgebra.counitAlgHom R (coordinateHopfAlgebra R n))))
      rfl (groupScheme_X_left_bundled R n)).2 (by
        rw [groupScheme_eq_asOver]
        exact heq_of_eq (AlgebraicGeometry.one_spec_asOver_spec_left
          (R := CommRingCat.of R)
          (A := CommRingCat.of (coordinateHopfAlgebra R n))))

private lemma groupScheme_mul_left_bundled :
    μ[(groupScheme R n).X].left =
      eqToHom (groupScheme_tensor_X_left_bundled R n) ≫
        (pullbackSpecIso R (coordinateHopfAlgebra R n)
          (coordinateHopfAlgebra R n)).hom ≫
        Spec.map (CommRingCat.ofHom
          (Bialgebra.comulAlgHom R (coordinateHopfAlgebra R n))) ≫
        eqToHom (groupScheme_X_left_bundled R n).symm := by
  simpa only [Category.assoc] using
    (conj_eqToHom_iff_heq
      μ[(groupScheme R n).X].left
      ((pullbackSpecIso R (coordinateHopfAlgebra R n)
          (coordinateHopfAlgebra R n)).hom ≫
        Spec.map (CommRingCat.ofHom
          (Bialgebra.comulAlgHom R (coordinateHopfAlgebra R n))))
      (groupScheme_tensor_X_left_bundled R n)
      (groupScheme_X_left_bundled R n)).2 (by
        rw [groupScheme_eq_asOver]
        exact heq_of_eq (AlgebraicGeometry.mul_spec_asOver_spec_left
          (R := CommRingCat.of R)
          (A := CommRingCat.of (coordinateHopfAlgebra R n))))

private lemma groupScheme_inv_left_bundled :
    ι[(groupScheme R n).X].left =
      eqToHom (groupScheme_X_left_bundled R n) ≫
        Spec.map (CommRingCat.ofHom
          (HopfAlgebra.antipodeAlgHom R (coordinateHopfAlgebra R n)).toRingHom) ≫
        eqToHom (groupScheme_X_left_bundled R n).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (groupScheme_X_left_bundled R n) (groupScheme_X_left_bundled R n)).2
  rw [groupScheme_eq_asOver]
  exact heq_of_eq (algSpec_map_left_ofAlgHom R
    (HopfAlgebra.antipodeAlgHom R (coordinateHopfAlgebra R n)))

/-- The unit of the general linear group scheme is induced by the raw coordinate counit. -/
@[simp]
lemma groupScheme_one_left :
    η[(groupScheme R n).X].left =
      Spec.map (CommRingCat.ofHom (counit R n).toRingHom) ≫
        (groupSchemeSpecIso R n).inv := by
  rw [groupScheme_one_left_bundled, groupSchemeSpecIso]
  simp only [Iso.trans_inv, eqToIso.inv,
    Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op,
    RingEquiv.toCommRingCatIso_inv]
  rw [← Category.assoc]
  apply (cancel_mono (eqToHom (groupScheme_X_left_bundled R n).symm)).2
  rw [← Spec.map_comp]
  rw [Spec.map_inj]
  ext x
  change Coalgebra.counit (R := R) (A := coordinateHopfAlgebra R n) x =
    counit R n ((coordinateHopfAlgebraAlgEquiv R n).symm x)
  simpa only [AlgEquiv.apply_symm_apply] using
      (coordinateHopfAlgebra_counit_apply R n
        ((coordinateHopfAlgebraAlgEquiv R n).symm x))

/-- Multiplication on the general linear group scheme is induced by the raw matrix-multiplication
comultiplication. The source presentation fixes the tensor-factor order representing ordinary
matrix multiplication. -/
@[simp]
lemma groupScheme_mul_left :
    μ[(groupScheme R n).X].left =
      (groupSchemeMulSourceIso R n).hom ≫
        Spec.map (CommRingCat.ofHom (comul R n).toRingHom) ≫
        (groupSchemeSpecIso R n).inv := by
  rw [groupScheme_mul_left_bundled, groupSchemeMulSourceIso, groupSchemeSpecIso]
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Iso.op_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op, RingEquiv.toCommRingCatIso_hom,
    Iso.trans_inv, eqToIso.inv, Functor.mapIso_inv, Iso.op_inv,
    RingEquiv.toCommRingCatIso_inv, Category.assoc]
  apply (cancel_epi (eqToHom (groupScheme_tensor_X_left_bundled R n))).2
  apply (cancel_epi
    (pullbackSpecIso R (coordinateHopfAlgebra R n)
      (coordinateHopfAlgebra R n)).hom).2
  simp only [← Category.assoc]
  apply (cancel_mono (eqToHom (groupScheme_X_left_bundled R n).symm)).2
  rw [← Spec.map_comp, ← Spec.map_comp]
  rw [Spec.map_inj]
  ext x
  change Coalgebra.comul (R := R) (A := coordinateHopfAlgebra R n) x =
    coordinateTensorAlgEquiv R n
      (comul R n ((coordinateHopfAlgebraAlgEquiv R n).symm x))
  simpa only [AlgEquiv.apply_symm_apply, coordinateTensorAlgEquiv,
    Algebra.TensorProduct.congr_apply] using
      (coordinateHopfAlgebra_comul_apply R n
        ((coordinateHopfAlgebraAlgEquiv R n).symm x))

/-- Inversion on the general linear group scheme is induced by the raw inverse-matrix antipode. -/
@[simp]
lemma groupScheme_inv_left :
    ι[(groupScheme R n).X].left =
      (groupSchemeSpecIso R n).hom ≫
        Spec.map (CommRingCat.ofHom (antipode R n).toRingHom) ≫
        (groupSchemeSpecIso R n).inv := by
  rw [groupScheme_inv_left_bundled, groupSchemeSpecIso]
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Iso.op_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op, RingEquiv.toCommRingCatIso_hom,
    Iso.trans_inv, eqToIso.inv, Functor.mapIso_inv, Iso.op_inv,
    RingEquiv.toCommRingCatIso_inv, Category.assoc]
  apply (cancel_epi (eqToHom (groupScheme_X_left_bundled R n))).2
  simp only [← Category.assoc]
  apply (cancel_mono (eqToHom (groupScheme_X_left_bundled R n).symm)).2
  rw [← Spec.map_comp, ← Spec.map_comp]
  rw [Spec.map_inj]
  ext x
  change HopfAlgebra.antipode R x =
    coordinateHopfAlgebraAlgEquiv R n
      (antipode R n ((coordinateHopfAlgebraAlgEquiv R n).symm x))
  simpa only [AlgEquiv.apply_symm_apply] using
    (coordinateHopfAlgebra_antipode_apply R n
      ((coordinateHopfAlgebraAlgEquiv R n).symm x))

/-- The general linear group scheme is affine. -/
instance isAffine_groupScheme : IsAffine (groupScheme R n).X.left := by
  exact .of_isIso (groupSchemeSpecIso R n).hom

/-- The structural morphism of the general linear group scheme is locally of finite type. -/
instance locallyOfFiniteType_groupScheme :
    LocallyOfFiniteType (groupScheme R n).X.hom := by
  rw [groupScheme_X_hom]
  letI : LocallyOfFiniteType (groupSchemeSpecIso R n).hom :=
    locallyOfFiniteType_of_isOpenImmersion _
  letI : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R n)))) := by
    change LocallyOfFiniteType
      (Spec (CommRingCat.of (CoordinateRing R n)) ↘ Spec (CommRingCat.of R))
    infer_instance
  exact locallyOfFiniteType_comp _ _

end GeneralLinear

end TauCeti
