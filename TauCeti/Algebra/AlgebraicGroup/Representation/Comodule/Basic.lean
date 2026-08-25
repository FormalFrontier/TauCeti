/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.ScalarExtension
public import TauCeti.Algebra.AlgebraicGroup.PointsFunctor
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction

import TauCeti.Algebra.Bialgebra.TensorProduct
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Point representations and comodules

Let `H` be a commutative Hopf algebra over a commutative ring `R`, and let `V` be an
`R`-module. This file identifies natural actions of the represented point groups

`A ↦ Hom_{R-alg}(H, A)`

on the scalar extensions `A ⊗[R] V` with right `H`-comodule structures on `V`. The base ring,
Hopf algebra, and module may lie in separate universes. The value-algebra category is placed in
their maximum universe, so the universal values `H`, `R`, and `H ⊗[R] H` are accessed through
their canonical universe lifts.

The action associated to a coaction `ρ(v) = ∑ v₀ ⊗ v₁` is characterized by

`(a ⊗ v) ↦ ∑ a * x(v₁) ⊗ v₀`

at a point `x : H →ₐ[R] A`. Conversely, the coaction is recovered by evaluating at the
universal point `id_H` and flipping the two tensor factors. The constructions are inverse without
any finiteness, freeness, projectivity, flatness, or nontriviality hypothesis.

## Main declarations

* `HopfAlgebra.PointRepresentation`: a natural action on the scalar extensions of `V`.
* `HopfAlgebra.PointRepresentation.ofComodule`: the point representation induced by a coaction.
* `HopfAlgebra.PointRepresentation.ofComodule_action_val_eq_endOfPoint`: identification of the
  induced representation action with the underlying comodule point action.
* `HopfAlgebra.PointRepresentation.toComodule`: recovery of a coaction from the universal point.
* `HopfAlgebra.pointRepresentationEquivComodule`: the fixed-object representation--comodule
  correspondence.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter VIII, §§2, 4, and 6.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a), Remark 4.1.
-/

public section

open CategoryTheory TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} {V : Type w} [CommRing R] [CommRing H]
variable [_root_.HopfAlgebra R H]
variable [AddCommMonoid V] [Module R V]

/-- A point representation of the affine group represented by `H` on an `R`-module `V`.

It is a natural family of group homomorphisms from the convolution group of `A`-points to the
linear automorphisms of `A ⊗[R] V`, for every commutative `R`-algebra `A`. -/
noncomputable abbrev PointRepresentation :=
  (pointsFunctor (R := R) (H := H) :
      CommAlgCat.{max u v w} R ⥤ GrpCat.{max u v w}) ⟶
    (GeneralLinear.scalarExtensionAutomorphismsFunctor (R := R) (V := V) :
      CommAlgCat.{max u v w} R ⥤ GrpCat.{max u v w})

namespace PointRepresentation

private noncomputable def liftedCounitAlgHom (_V : Type w) :
    ULift.{max u v w} H →ₐ[R] ULift.{max u v w} R :=
  ULift.algEquiv.symm.toAlgHom.comp
    ((Bialgebra.counitAlgHom R H).comp ULift.algEquiv.toAlgHom)

private noncomputable def liftedComulAlgHom (_V : Type w) :
    ULift.{max u v w} H →ₐ[R] ULift.{max u v w} (H ⊗[R] H) :=
  ULift.algEquiv.symm.toAlgHom.comp
    ((Bialgebra.comulAlgHom R H).comp ULift.algEquiv.toAlgHom)

/-- The group homomorphism at a value algebra, with the opaque functor object equalities removed. -/
noncomputable def action (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (A : CommAlgCat.{max u v w} R) :
    points (H := H) A ⟶ GeneralLinear.scalarExtensionAutomorphisms (V := V) A :=
  Theta.app A ≫
    eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A)

/-- The concrete point action is the natural-transformation component followed by the canonical
scalar-extension functor-object transport. -/
theorem action_def (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (A : CommAlgCat.{max u v w} R) :
    Theta.action A =
      Theta.app A ≫
        eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A) := by
  rfl

/-- Point representations are equal when their concrete actions agree at every value algebra and
point. -/
@[ext]
theorem ext
    {Theta Psi : PointRepresentation (R := R) (H := H) (V := V)}
    (h : ∀ (A : CommAlgCat.{max u v w} R) (x : points (H := H) A),
      Theta.action A x = Psi.action A x) :
    Theta = Psi := by
  apply NatTrans.ext
  funext A
  apply (cancel_mono
    (eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A))).1
  -- Once the opaque functor-object transport is cancelled, the concrete-action wrapper unfolds
  -- definitionally to the remaining natural-transformation component.
  change Theta.action A = Psi.action A
  apply GrpCat.ext
  intro x
  exact h A x

/-- Naturality of a point representation, expressed using the concrete point and scalar-extension
groups. -/
theorem action_naturality (Theta : PointRepresentation (R := R) (H := H) (V := V))
    {A B : CommAlgCat.{max u v w} R} (phi : A ⟶ B) (x : points (H := H) A) :
    GeneralLinear.mapScalarExtensionAutomorphisms (V := V) phi (Theta.action A x) =
      Theta.action B (mapPoints (H := H) phi x) := by
  have h := Theta.naturality phi
  have h' := congrArg (fun f ↦
    f ≫ eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) B)) h
  simp only [pointsFunctor_map, GeneralLinear.scalarExtensionAutomorphismsFunctor_map,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h'
  exact (ConcreteCategory.congr_hom h'.symm x)

/-- Naturality determines the action of a transported point on the canonical copy of `V`. -/
@[simp]
theorem action_mapPoints_one_tmul
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    {A B : CommAlgCat.{max u v w} R} (phi : A ⟶ B) (x : points (H := H) A) (v : V) :
    (Theta.action B (mapPoints (H := H) phi x)).val (1 ⊗ₜ[R] v) =
      GeneralLinear.scalarExtensionMap (V := V) phi
        ((Theta.action A x).val (1 ⊗ₜ[R] v)) := by
  rw [← Theta.action_naturality phi x]
  simpa using
    (GeneralLinear.mapScalarExtensionAutomorphisms_apply_scalarExtensionMap
      (V := V) phi (Theta.action A x) (1 ⊗ₜ[R] v))

private noncomputable def rawPointAction (rho : Comodule R H V)
    (A : CommAlgCat.{max u v w} R) :
    points (H := H) A ⟶ GeneralLinear.scalarExtensionAutomorphisms (V := V) A := by
  letI : Comodule R H V := rho
  exact GrpCat.ofHom <|
    (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[R] V)).symm.toMonoidHom.comp
      (Comodule.pointsAction V)

@[simp]
private theorem rawPointAction_apply (rho : Comodule R H V)
    (A : CommAlgCat.{max u v w} R) (x : points (H := H) A) :
    rawPointAction rho A x =
      let _ : Comodule R H V := rho
      (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[R] V)).symm
        (Comodule.pointsAction V x) := by
  rfl

@[simp]
private theorem rawPointAction_val (rho : Comodule R H V)
    (A : CommAlgCat.{max u v w} R) (x : points (H := H) A) :
    (rawPointAction rho A x).val = Comodule.endOfPoint V x.ofConv := by
  let : Comodule R H V := rho
  rw [rawPointAction_apply]
  exact Comodule.pointsAction_toLinearMap V x

private theorem rawPointAction_naturality (rho : Comodule R H V)
    {A B : CommAlgCat.{max u v w} R} (phi : A ⟶ B) (x : points (H := H) A) :
    GeneralLinear.mapScalarExtensionAutomorphisms (V := V) phi (rawPointAction rho A x) =
      rawPointAction rho B (mapPoints (H := H) phi x) := by
  symm
  apply GeneralLinear.eq_mapScalarExtensionAutomorphisms_of_apply_scalarExtensionMap_eq
    (V := V) phi (rawPointAction rho A x)
      (rawPointAction rho B (mapPoints (H := H) phi x))
  intro z
  rw [rawPointAction_val, rawPointAction_val]
  let : Comodule R H V := rho
  have hscalar :
      GeneralLinear.scalarExtensionMap (V := V) phi =
        LinearMap.rTensor V phi.hom.toLinearMap := by
    refine TensorProduct.ext' fun a v ↦ ?_
    rw [GeneralLinear.scalarExtensionMap_tmul, LinearMap.rTensor_tmul]
    rfl
  have hpoint :
      (mapPoints (H := H) phi x).ofConv = phi.hom.comp x.ofConv := by
    rfl
  have h := DFunLike.congr_fun
    (Comodule.rTensor_comp_endOfPoint V phi.hom x.ofConv) z
  rw [hscalar, hpoint]
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h.symm

/-- The natural point representation induced by a right `H`-comodule structure. -/
noncomputable def ofComodule (rho : Comodule R H V) :
    PointRepresentation (R := R) (H := H) (V := V) where
  app A := rawPointAction rho A ≫
    eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A).symm
  naturality A B phi := by
    -- `pointsFunctor_obj` and the scalar-extension object theorem are categorical equalities,
    -- with no computation lemma that rewrites this structure-field goal before it is exposed.
    change
      mapPoints (H := H) phi ≫ rawPointAction rho B ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) B).symm =
        rawPointAction rho A ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A).symm ≫
          (GeneralLinear.scalarExtensionAutomorphismsFunctor (V := V)).map phi
    have hraw :
        mapPoints (H := H) phi ≫ rawPointAction rho B =
          rawPointAction rho A ≫
            GeneralLinear.mapScalarExtensionAutomorphisms (V := V) phi := by
      apply GrpCat.ext
      intro x
      exact (rawPointAction_naturality rho phi x).symm
    rw [GeneralLinear.scalarExtensionAutomorphismsFunctor_map]
    rw [← Category.assoc, hraw]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

@[simp]
private theorem action_ofComodule (rho : Comodule R H V)
    (A : CommAlgCat.{max u v w} R) :
    (ofComodule rho).action A = rawPointAction rho A := by
  rw [action, ofComodule]
  -- The natural-transformation component is stored with the inverse of the opaque object
  -- equality; expose that categorical composite before cancelling the two transports.
  change
    (rawPointAction rho A ≫
        eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A).symm) ≫
      eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A) =
        rawPointAction rho A
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The action induced by a coaction, evaluated on a pure tensor. -/
@[simp]
theorem ofComodule_action_tmul (rho : Comodule R H V)
    (A : CommAlgCat.{max u v w} R)
    (x : points (H := H) A) (a : A) (v : V) :
    ((ofComodule rho).action A x).val (a ⊗ₜ[R] v) =
      a • TensorProduct.comm R V A
        (TensorProduct.map LinearMap.id x.ofConv.toLinearMap (rho.coact v)) := by
  rw [action_ofComodule]
  rw [rawPointAction_val]
  let : Comodule R H V := rho
  simpa only [LinearMap.lTensor_def] using
    (Comodule.endOfPoint_tmul (R := R) (H := H) V x.ofConv a v)

/-- The underlying linear map of the action induced by a coaction is the corresponding
comodule point-action endomorphism. -/
theorem ofComodule_action_val_eq_endOfPoint (rho : Comodule R H V)
    (A : CommAlgCat.{max u v w} R) (x : points (H := H) A) :
    ((ofComodule rho).action A x).val = Comodule.endOfPoint V x.ofConv := by
  refine TensorProduct.AlgebraTensorModule.ext fun a v ↦ ?_
  rw [ofComodule_action_tmul, Comodule.endOfPoint_tmul, LinearMap.lTensor_def]

/-- At the universal point, the action induced by a coaction is the flipped coaction. -/
@[simp]
theorem ofComodule_action_universal_one_tmul (rho : Comodule R H V) (v : V) :
    ((ofComodule rho).action (CommAlgCat.of R (ULift.{max u v w} H))
        (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[R] v) =
      TensorProduct.comm R V (ULift.{max u v w} H)
        (TensorProduct.map LinearMap.id ULift.algEquiv.symm.toLinearMap (rho.coact v)) := by
  rw [ofComodule_action_tmul]
  exact one_smul (ULift.{max u v w} H)
    (TensorProduct.comm R V (ULift.{max u v w} H)
      (TensorProduct.map LinearMap.id ULift.algEquiv.symm.toLinearMap (rho.coact v)))

private noncomputable def universalGenerator
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    V →ₗ[R] ULift.{max u v w} H ⊗[R] V :=
  ((Theta.action (CommAlgCat.of R (ULift.{max u v w} H))
      (toConv ULift.algEquiv.symm.toAlgHom)).val.restrictScalars R) ∘ₗ
    TensorProduct.mk R (ULift.{max u v w} H) V 1

private noncomputable def universalGeneratorDown
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    V →ₗ[R] H ⊗[R] V :=
  TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id ∘ₗ universalGenerator Theta

private noncomputable def recoveredCoaction
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    V →ₗ[R] V ⊗[R] H :=
  (TensorProduct.comm R H V).toLinearMap ∘ₗ universalGeneratorDown Theta

@[simp]
private theorem universalGenerator_apply
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    universalGenerator Theta v =
      (Theta.action (CommAlgCat.of R (ULift.{max u v w} H))
        (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[R] v) :=
  rfl

@[simp]
private theorem universalGeneratorDown_apply
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    universalGeneratorDown Theta v =
      TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id (universalGenerator Theta v) :=
  rfl

@[simp]
private theorem recoveredCoaction_apply
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    recoveredCoaction Theta v = TensorProduct.comm R H V (universalGeneratorDown Theta v) :=
  rfl

omit [AddCommMonoid V] [Module R V] in
private theorem mapPoints_universal {A : Type (max u v w)} [CommRing A] [Algebra R A]
    (phi : ULift.{max u v w} H →ₐ[R] A) :
    mapPoints (H := H) (CommAlgCat.ofHom phi)
        (toConv ULift.algEquiv.symm.toAlgHom) =
      toConv (phi.comp ULift.algEquiv.symm.toAlgHom) := by
  rfl

omit [AddCommMonoid V] [Module R V] in
private theorem mapPoints_universal_counit :
    mapPoints (H := H) (CommAlgCat.ofHom (liftedCounitAlgHom (R := R) (H := H) V))
        (toConv ULift.algEquiv.symm.toAlgHom) = 1 := by
  rw [mapPoints_universal]
  apply WithConv.ofConv_injective
  ext h
  simp only [AlgHom.convOne_apply, Bialgebra.counitAlgHom_apply, AlgHom.coe_comp,
    Function.comp_apply, liftedCounitAlgHom]
  rfl

private theorem scalarExtensionMap_counit_universalGenerator
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    GeneralLinear.scalarExtensionMap (V := V)
        (CommAlgCat.ofHom (liftedCounitAlgHom (R := R) (H := H) V))
          (universalGenerator Theta v) =
      1 ⊗ₜ[R] v := by
  have h := Theta.action_mapPoints_one_tmul
    (CommAlgCat.ofHom (liftedCounitAlgHom (R := R) (H := H) V))
      (toConv ULift.algEquiv.symm.toAlgHom) v
  rw [mapPoints_universal_counit,
    (Theta.action (CommAlgCat.of R (ULift.{max u v w} R))).hom.map_one] at h
  simpa only [universalGenerator_apply, Units.val_one, Module.End.one_apply] using h.symm

private theorem counit_rTensor_universalGeneratorDown
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    Coalgebra.counit.rTensor V (universalGeneratorDown Theta v) = 1 ⊗ₜ[R] v := by
  have hvalue := scalarExtensionMap_counit_universalGenerator Theta v
  have h := congrArg
    (TensorProduct.map (R := R) ULift.algEquiv.toLinearMap LinearMap.id)
    hvalue
  have hmap : ∀ z : ULift.{max u v w} H ⊗[R] V,
      TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
          (GeneralLinear.scalarExtensionMap (V := V)
            (CommAlgCat.ofHom (liftedCounitAlgHom (R := R) (H := H) V)) z) =
        Coalgebra.counit.rTensor V
          (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z t hz ht => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hz ht
    | tmul a n =>
        rw [GeneralLinear.scalarExtensionMap_tmul]
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.rTensor_tmul]
        rfl
  rw [hmap] at h
  have hone : (ULift.algEquiv (R := R) (A := R)).toLinearMap
      (1 : ULift.{max u v w} R) = 1 := rfl
  simp only [TensorProduct.map_tmul, LinearMap.id_apply] at h
  rw [hone] at h
  simpa only [universalGeneratorDown_apply] using h

private theorem recoveredCoaction_counit
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    Coalgebra.counit.lTensor V ∘ₗ recoveredCoaction Theta =
      (TensorProduct.mk R V R).flip 1 := by
  apply LinearMap.ext
  intro v
  apply (TensorProduct.comm R V R).injective
  simp only [LinearMap.comp_apply]
  rw [recoveredCoaction_apply]
  have hcomm :
      TensorProduct.comm R V R
          (Coalgebra.counit.lTensor V
            (TensorProduct.comm R H V (universalGeneratorDown Theta v))) =
        Coalgebra.counit.rTensor V (universalGeneratorDown Theta v) := by
    exact LinearMap.congr_fun
      (LinearMap.comm_comp_lTensor_comp_comm_eq (Q := V) Coalgebra.counit)
      (universalGeneratorDown Theta v)
  rw [hcomm]
  simp only [LinearMap.flip_apply, TensorProduct.mk_apply, TensorProduct.comm_tmul]
  exact counit_rTensor_universalGeneratorDown Theta v

private noncomputable abbrev includeLeftAlgHom : H →ₐ[R] H ⊗[R] H :=
  (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := H)).toAlgHom

private noncomputable abbrev includeRightAlgHom : H →ₐ[R] H ⊗[R] H :=
  (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := H)).toAlgHom

private theorem includeRight_mul_includeLeft (a b : H) :
    includeRightAlgHom (R := R) (H := H) a *
        includeLeftAlgHom (R := R) (H := H) b =
      b ⊗ₜ[R] a := by
  have hleft : includeLeftAlgHom (R := R) (H := H) b = b ⊗ₜ[R] 1 :=
    Bialgebra.TensorProduct.includeLeft_apply b
  have hright : includeRightAlgHom (R := R) (H := H) a = 1 ⊗ₜ[R] a :=
    Bialgebra.TensorProduct.includeRight_apply a
  rw [hleft, hright, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private noncomputable def liftedIncludeLeftAlgHom (_V : Type w) :
    ULift.{max u v w} H →ₐ[R] ULift.{max u v w} (H ⊗[R] H) :=
  ULift.algEquiv.symm.toAlgHom.comp
    ((includeLeftAlgHom (R := R) (H := H)).comp ULift.algEquiv.toAlgHom)

private noncomputable def liftedIncludeRightAlgHom (_V : Type w) :
    ULift.{max u v w} H →ₐ[R] ULift.{max u v w} (H ⊗[R] H) :=
  ULift.algEquiv.symm.toAlgHom.comp
    ((includeRightAlgHom (R := R) (H := H)).comp ULift.algEquiv.toAlgHom)

private noncomputable def liftTensorSquare :
    (H ⊗[R] H) ⊗[R] V ≃ₗ[R] ULift.{max u v w} (H ⊗[R] H) ⊗[R] V :=
  TensorProduct.congr ULift.algEquiv.symm.toLinearEquiv (LinearEquiv.refl R V)

omit [AddCommMonoid V] [Module R V] in
@[simp]
private theorem ofHom_liftedIncludeLeft_apply (a : ULift.{max u v w} H) :
    (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V)).hom a =
      liftedIncludeLeftAlgHom (R := R) (H := H) V a :=
  rfl

omit [AddCommMonoid V] [Module R V] in
@[simp]
private theorem ofHom_liftedIncludeRight_apply (a : ULift.{max u v w} H) :
    (CommAlgCat.ofHom (liftedIncludeRightAlgHom (R := R) (H := H) V)).hom a =
      liftedIncludeRightAlgHom (R := R) (H := H) V a :=
  rfl

omit [AddCommMonoid V] [Module R V] in
@[simp]
private theorem ofHom_liftedComul_apply (a : ULift.{max u v w} H) :
    (CommAlgCat.ofHom (liftedComulAlgHom (R := R) (H := H) V)).hom a =
      liftedComulAlgHom (R := R) (H := H) V a :=
  rfl

omit [AddCommMonoid V] [Module R V] in
private theorem liftedComulPoint_eq_include_mul :
    mapPoints (H := H)
        (CommAlgCat.ofHom (liftedComulAlgHom (R := R) (H := H) V))
          (toConv ULift.algEquiv.symm.toAlgHom) =
      mapPoints (H := H)
          (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V))
            (toConv ULift.algEquiv.symm.toAlgHom) *
        mapPoints (H := H)
          (CommAlgCat.ofHom (liftedIncludeRightAlgHom (R := R) (H := H) V))
            (toConv ULift.algEquiv.symm.toAlgHom) := by
  rw [mapPoints_universal, mapPoints_universal, mapPoints_universal]
  let up : H ⊗[R] H →ₐ[R] ULift.{max u v w} (H ⊗[R] H) :=
    ULift.algEquiv.symm.toAlgHom
  have hcomul :
      (liftedComulAlgHom (R := R) (H := H) V).comp ULift.algEquiv.symm.toAlgHom =
        up.comp (Bialgebra.comulAlgHom R H) := by
    ext h
    rfl
  have hleft :
      (liftedIncludeLeftAlgHom (R := R) (H := H) V).comp
          ULift.algEquiv.symm.toAlgHom =
        up.comp (includeLeftAlgHom (R := R) (H := H)) := by
    ext h
    rfl
  have hright :
      (liftedIncludeRightAlgHom (R := R) (H := H) V).comp
          ULift.algEquiv.symm.toAlgHom =
        up.comp (includeRightAlgHom (R := R) (H := H)) := by
    ext h
    rfl
  rw [hcomul, hleft, hright]
  exact Bialgebra.toConv_comp_comulAlgHom up

private theorem action_comul_eq_include_actions
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
        (mapPoints (H := H)
          (CommAlgCat.ofHom (liftedComulAlgHom (R := R) (H := H) V))
            (toConv ULift.algEquiv.symm.toAlgHom)) =
      Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
          (mapPoints (H := H)
            (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V))
              (toConv ULift.algEquiv.symm.toAlgHom)) *
        Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
          (mapPoints (H := H)
            (CommAlgCat.ofHom (liftedIncludeRightAlgHom (R := R) (H := H) V))
              (toConv ULift.algEquiv.symm.toAlgHom)) := by
  rw [liftedComulPoint_eq_include_mul]
  exact (Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))).hom.map_mul _ _

private theorem action_includeLeft_includeRight_tmul
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (a : ULift.{max u v w} H) (n : V) :
    (Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
        (mapPoints (H := H)
          (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V))
            (toConv ULift.algEquiv.symm.toAlgHom))).val
      (liftedIncludeRightAlgHom (R := R) (H := H) V a ⊗ₜ[R] n) =
      liftedIncludeRightAlgHom (R := R) (H := H) V a •
        GeneralLinear.scalarExtensionMap (V := V)
          (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V))
            (universalGenerator Theta n) := by
  rw [TensorProduct.tmul_eq_smul_one_tmul (M := V), map_smul,
    Theta.action_mapPoints_one_tmul
      (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V))
        (toConv ULift.algEquiv.symm.toAlgHom) n]
  rw [universalGenerator_apply]

private theorem liftTensorSquare_iterated_tmul
    (a : ULift.{max u v w} H) (z : ULift.{max u v w} H ⊗[R] V) :
    liftTensorSquare (R := R) (H := H) (V := V)
        (TensorProduct.comm R V (H ⊗[R] H)
          (TensorProduct.assoc R V H H
            (TensorProduct.comm R H V
                (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id z) ⊗ₜ[R]
              a.down))) =
      liftedIncludeRightAlgHom (R := R) (H := H) V a •
        GeneralLinear.scalarExtensionMap (V := V)
          (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht =>
      simpa only [map_add, TensorProduct.add_tmul, smul_add] using
        congrArg₂ (fun x y ↦ x + y) hz ht
  | tmul b n =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.comm_tmul,
        TensorProduct.assoc_tmul]
      rw [GeneralLinear.scalarExtensionMap_tmul]
      rw [ofHom_liftedIncludeLeft_apply]
      simp only [liftTensorSquare, TensorProduct.congr_tmul]
      apply congrArg (fun c : ULift.{max u v w} (H ⊗[R] H) ↦ c ⊗ₜ[R] n)
      apply ULift.down_injective
      exact (includeRight_mul_includeLeft (R := R) (H := H) a.down b.down).symm

private theorem recoveredCoaction_iterate_eq_include_actions
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    liftTensorSquare (R := R) (H := H) (V := V)
        (TensorProduct.comm R V (H ⊗[R] H)
          (TensorProduct.assoc R V H H
            ((recoveredCoaction Theta).rTensor H (recoveredCoaction Theta v)))) =
      (Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
          (mapPoints (H := H)
            (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V))
              (toConv ULift.algEquiv.symm.toAlgHom))).val
        ((Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
            (mapPoints (H := H)
              (CommAlgCat.ofHom (liftedIncludeRightAlgHom (R := R) (H := H) V))
                (toConv ULift.algEquiv.symm.toAlgHom))).val (1 ⊗ₜ[R] v)) := by
  rw [Theta.action_mapPoints_one_tmul
    (CommAlgCat.ofHom (liftedIncludeRightAlgHom (R := R) (H := H) V))
      (toConv ULift.algEquiv.symm.toAlgHom) v]
  rw [← universalGenerator_apply]
  have hz : ∀ z : ULift.{max u v w} H ⊗[R] V,
      liftTensorSquare (R := R) (H := H) (V := V)
          (TensorProduct.comm R V (H ⊗[R] H)
            (TensorProduct.assoc R V H H
              ((recoveredCoaction Theta).rTensor H
                (TensorProduct.comm R H V
                  (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id z))))) =
        (Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
            (mapPoints (H := H)
              (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V))
                (toConv ULift.algEquiv.symm.toAlgHom))).val
          (GeneralLinear.scalarExtensionMap (V := V)
            (CommAlgCat.ofHom (liftedIncludeRightAlgHom (R := R) (H := H) V)) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) hz hw
    | tmul a n =>
        rw [GeneralLinear.scalarExtensionMap_tmul]
        rw [ofHom_liftedIncludeRight_apply]
        rw [action_includeLeft_includeRight_tmul]
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.comm_tmul,
          LinearMap.rTensor_tmul, recoveredCoaction_apply, universalGeneratorDown_apply]
        exact liftTensorSquare_iterated_tmul a (universalGenerator Theta n)
  rw [recoveredCoaction_apply, universalGeneratorDown_apply]
  exact hz (universalGenerator Theta v)

private theorem scalarExtensionMap_comul_eq_liftTensorSquare
    (z : ULift.{max u v w} H ⊗[R] V) :
    GeneralLinear.scalarExtensionMap (V := V)
        (CommAlgCat.ofHom (liftedComulAlgHom (R := R) (H := H) V)) z =
      liftTensorSquare (R := R) (H := H) (V := V)
        (Coalgebra.comul.rTensor V
          (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hz ht
  | tmul a n =>
      rw [GeneralLinear.scalarExtensionMap_tmul, ofHom_liftedComul_apply,
        TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      simp only [liftTensorSquare, TensorProduct.congr_tmul]
      rfl

private theorem include_actions_eq_scalarExtensionMap_comul
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    (Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
        (mapPoints (H := H)
          (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V))
            (toConv ULift.algEquiv.symm.toAlgHom))).val
      ((Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
          (mapPoints (H := H)
            (CommAlgCat.ofHom (liftedIncludeRightAlgHom (R := R) (H := H) V))
              (toConv ULift.algEquiv.symm.toAlgHom))).val (1 ⊗ₜ[R] v)) =
      GeneralLinear.scalarExtensionMap (V := V)
        (CommAlgCat.ofHom (liftedComulAlgHom (R := R) (H := H) V))
          (universalGenerator Theta v) := by
  have hvalue := congrArg
    (fun g : GeneralLinear.scalarExtensionAutomorphisms (V := V)
        (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H))) ↦ g.val (1 ⊗ₜ[R] v))
    (action_comul_eq_include_actions Theta)
  have hnatural := Theta.action_mapPoints_one_tmul
    (CommAlgCat.ofHom (liftedComulAlgHom (R := R) (H := H) V))
      (toConv ULift.algEquiv.symm.toAlgHom) v
  have hcompose :
      (Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
          (mapPoints (H := H)
            (CommAlgCat.ofHom (liftedComulAlgHom (R := R) (H := H) V))
              (toConv ULift.algEquiv.symm.toAlgHom))).val (1 ⊗ₜ[R] v) =
        (Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
            (mapPoints (H := H)
              (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V))
                (toConv ULift.algEquiv.symm.toAlgHom))).val
          ((Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
              (mapPoints (H := H)
                (CommAlgCat.ofHom (liftedIncludeRightAlgHom (R := R) (H := H) V))
                  (toConv ULift.algEquiv.symm.toAlgHom))).val (1 ⊗ₜ[R] v)) := by
    simpa only [Units.val_mul, Module.End.mul_apply] using hvalue
  rw [← hcompose, hnatural]
  rw [universalGenerator_apply]

private theorem recoveredCoaction_coassoc
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    TensorProduct.assoc R V H H ∘ₗ (recoveredCoaction Theta).rTensor H ∘ₗ
        recoveredCoaction Theta =
      Coalgebra.comul.lTensor V ∘ₗ recoveredCoaction Theta := by
  apply LinearMap.ext
  intro v
  apply (TensorProduct.comm R V (H ⊗[R] H)).injective
  apply (liftTensorSquare (R := R) (H := H) (V := V)).injective
  simp only [LinearMap.comp_apply]
  calc
    _ =
        (Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
            (mapPoints (H := H)
              (CommAlgCat.ofHom (liftedIncludeLeftAlgHom (R := R) (H := H) V))
                (toConv ULift.algEquiv.symm.toAlgHom))).val
          ((Theta.action (CommAlgCat.of R (ULift.{max u v w} (H ⊗[R] H)))
              (mapPoints (H := H)
                (CommAlgCat.ofHom (liftedIncludeRightAlgHom (R := R) (H := H) V))
                  (toConv ULift.algEquiv.symm.toAlgHom))).val (1 ⊗ₜ[R] v)) :=
      recoveredCoaction_iterate_eq_include_actions Theta v
    _ = GeneralLinear.scalarExtensionMap (V := V)
          (CommAlgCat.ofHom (liftedComulAlgHom (R := R) (H := H) V))
            (universalGenerator Theta v) :=
      include_actions_eq_scalarExtensionMap_comul Theta v
    _ = liftTensorSquare (R := R) (H := H) (V := V)
          (Coalgebra.comul.rTensor V (universalGeneratorDown Theta v)) := by
      simpa only [universalGeneratorDown_apply] using
        scalarExtensionMap_comul_eq_liftTensorSquare (R := R) (H := H) (V := V)
          (universalGenerator Theta v)
    _ = _ := by
      rw [recoveredCoaction_apply]
      have hcomm :
          TensorProduct.comm R V (H ⊗[R] H)
              (Coalgebra.comul.lTensor V
                (TensorProduct.comm R H V (universalGeneratorDown Theta v))) =
            Coalgebra.comul.rTensor V (universalGeneratorDown Theta v) := by
        exact LinearMap.congr_fun
          (LinearMap.comm_comp_lTensor_comp_comm_eq (Q := V) Coalgebra.comul)
          (universalGeneratorDown Theta v)
      rw [hcomm]

/-- Recover a right `H`-comodule structure from a natural point representation by evaluating at
the universal point and flipping the tensor factors. The definition is intentionally opaque; use
`toComodule_coact_apply` to expose its coaction. -/
@[irreducible]
noncomputable def toComodule
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) : Comodule R H V where
  coact := recoveredCoaction Theta
  coassoc := recoveredCoaction_coassoc Theta
  lTensor_counit_comp_coact := recoveredCoaction_counit Theta

/-- The coaction recovered from a point representation is the flipped universal-point action. -/
@[simp]
theorem toComodule_coact_apply
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    (toComodule Theta).coact v =
      TensorProduct.comm R H V
        (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
          ((Theta.action (CommAlgCat.of R (ULift.{max u v w} H))
            (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[R] v))) :=
  by
    unfold toComodule
    rfl

/-- Recovering a comodule from its induced point representation returns the original comodule. -/
@[simp]
theorem toComodule_ofComodule (rho : Comodule R H V) :
    toComodule (ofComodule rho) = rho := by
  apply Comodule.ext
  apply LinearMap.ext
  intro v
  rw [toComodule_coact_apply, ofComodule_action_universal_one_tmul]
  induction rho.coact v using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hz ht
  | tmul n h =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.comm_tmul]
      rfl

private theorem mapPoints_universal_ofConv
    {A : CommAlgCat.{max u v w} R} (x : points (H := H) A) :
    mapPoints (H := H)
        (CommAlgCat.ofHom (x.ofConv.comp
          (ULift.algEquiv (R := R) : ULift.{max u v w} H ≃ₐ[R] H).toAlgHom))
          (toConv ULift.algEquiv.symm.toAlgHom) = x := by
  rw [mapPoints_universal]
  apply WithConv.ofConv_injective
  ext h
  rfl

/-- Reconstructing the point representation from its recovered comodule returns the original
natural action. -/
@[simp]
theorem ofComodule_toComodule
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    ofComodule (toComodule Theta) = Theta := by
  have huniversal :
      (ofComodule (toComodule Theta)).action
          (CommAlgCat.of R (ULift.{max u v w} H))
            (toConv ULift.algEquiv.symm.toAlgHom) =
        Theta.action (CommAlgCat.of R (ULift.{max u v w} H))
          (toConv ULift.algEquiv.symm.toAlgHom) := by
    apply Units.ext
    refine TensorProduct.AlgebraTensorModule.ext fun a v ↦ ?_
    rw [TensorProduct.tmul_eq_smul_one_tmul (M := V), map_smul, map_smul]
    congr 1
    rw [ofComodule_action_universal_one_tmul, toComodule_coact_apply]
    induction (Theta.action (CommAlgCat.of R (ULift.{max u v w} H))
        (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[R] v)
        using TensorProduct.induction_on with
    | zero => simp
    | add z t hz ht => simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hz ht
    | tmul h n =>
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.comm_tmul]
        rfl
  have haction : ∀ (A : CommAlgCat.{max u v w} R) (x : points (H := H) A),
      (ofComodule (toComodule Theta)).action A x = Theta.action A x := by
    intro A x
    have hforward := (ofComodule (toComodule Theta)).action_naturality
      (CommAlgCat.ofHom (x.ofConv.comp
        (ULift.algEquiv (R := R) : ULift.{max u v w} H ≃ₐ[R] H).toAlgHom))
        (toConv ULift.algEquiv.symm.toAlgHom)
    have hTheta := Theta.action_naturality
      (CommAlgCat.ofHom (x.ofConv.comp
        (ULift.algEquiv (R := R) : ULift.{max u v w} H ≃ₐ[R] H).toAlgHom))
        (toConv ULift.algEquiv.symm.toAlgHom)
    rw [mapPoints_universal_ofConv, huniversal] at hforward
    rw [mapPoints_universal_ofConv] at hTheta
    exact hforward.symm.trans hTheta
  exact ext haction

end PointRepresentation

/-- Natural point representations on `V` are equivalent to right `H`-comodule structures on
`V`. -/
noncomputable def pointRepresentationEquivComodule :
    PointRepresentation (R := R) (H := H) (V := V) ≃ Comodule R H V where
  toFun := PointRepresentation.toComodule
  invFun := PointRepresentation.ofComodule
  left_inv := PointRepresentation.ofComodule_toComodule
  right_inv := PointRepresentation.toComodule_ofComodule

/-- The forward map of the representation--comodule equivalence recovers the coaction at the
universal point. -/
@[simp]
theorem pointRepresentationEquivComodule_apply
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    pointRepresentationEquivComodule Theta = PointRepresentation.toComodule Theta :=
  by
    unfold pointRepresentationEquivComodule
    rfl

/-- The inverse map of the representation--comodule equivalence is the point action induced by a
coaction. -/
@[simp]
theorem pointRepresentationEquivComodule_symm_apply (rho : Comodule R H V) :
    pointRepresentationEquivComodule.symm rho = PointRepresentation.ofComodule rho :=
  by
    unfold pointRepresentationEquivComodule
    rfl

end HopfAlgebra

end TauCeti
