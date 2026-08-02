/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.ScalarExtension
public import TauCeti.Algebra.AlgebraicGroup.PointsFunctor
public import TauCeti.Algebra.Coalgebra.Comodule.Basic

import TauCeti.Algebra.Bialgebra.TensorProduct

/-!
# Point representations and comodules

Let `H` be a commutative Hopf algebra over a commutative ring `R`, and let `V` be an
`R`-module. This file identifies natural actions of the represented point groups

`A ↦ Hom_{R-alg}(H, A)`

on the scalar extensions `A ⊗[R] V` with right `H`-comodule structures on `V`. Both `H` and
the value algebras are kept in the same universe as `R` and `V`, so the universal point of `H`
and the tensor-square value algebra can be used directly.

The action associated to a coaction `ρ(v) = ∑ v₀ ⊗ v₁` is characterized by

`(a ⊗ v) ↦ ∑ a * x(v₁) ⊗ v₀`

at a point `x : H →ₐ[R] A`. Conversely, the coaction is recovered by evaluating at the
universal point `id_H` and flipping the two tensor factors. The constructions are inverse without
any finiteness, freeness, projectivity, flatness, or nontriviality hypothesis.

## Main declarations

* `HopfAlgebra.PointRepresentation`: a natural action on the scalar extensions of `V`.
* `HopfAlgebra.PointRepresentation.ofComodule`: the point representation induced by a coaction.
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

universe u

variable {R H V : Type u} [CommRing R] [CommRing H]
variable [_root_.HopfAlgebra R H]
variable [AddCommMonoid V] [Module R V]

/-- A point representation of the affine group represented by `H` on an `R`-module `V`.

It is a natural family of group homomorphisms from the convolution group of `A`-points to the
linear automorphisms of `A ⊗[R] V`, for every commutative `R`-algebra `A`. -/
noncomputable abbrev PointRepresentation :=
  pointsFunctor (R := R) (H := H) ⟶
    GeneralLinear.scalarExtensionAutomorphismsFunctor (R := R) (V := V)

namespace PointRepresentation

/-- The group homomorphism at a value algebra, with the opaque functor object equalities removed. -/
noncomputable def action (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (A : CommAlgCat.{u} R) :
    points (H := H) A ⟶ GeneralLinear.scalarExtensionAutomorphisms (V := V) A :=
  Theta.app A ≫
    eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A)

/-- Naturality of a point representation, expressed using the concrete point and scalar-extension
groups. -/
theorem action_naturality (Theta : PointRepresentation (R := R) (H := H) (V := V))
    {A B : CommAlgCat.{u} R} (phi : A ⟶ B) (x : points (H := H) A) :
    GeneralLinear.mapScalarExtensionAutomorphisms (V := V) phi (Theta.action A x) =
      Theta.action B (mapPoints (H := H) phi x) := by
  have h := Theta.naturality phi
  have h' := congrArg (fun f ↦
    f ≫ eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) B)) h
  simp only [pointsFunctor_map, GeneralLinear.scalarExtensionAutomorphismsFunctor_map,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h'
  have h'' := congrArg (fun f ↦ f x) h'.symm
  change
    GeneralLinear.mapScalarExtensionAutomorphisms (V := V) phi
        ((Theta.app A ≫
          eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A)) x) =
      (Theta.app B ≫
          eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) B))
        (mapPoints (H := H) phi x) at h''
  exact h''

/-- Naturality determines the action of a transported point on the canonical copy of `V`. -/
@[simp]
theorem action_mapPoints_one_tmul
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    {A B : CommAlgCat.{u} R} (phi : A ⟶ B) (x : points (H := H) A) (v : V) :
    (Theta.action B (mapPoints (H := H) phi x)).val (1 ⊗ₜ[R] v) =
      GeneralLinear.scalarExtensionMap (V := V) phi
        ((Theta.action A x).val (1 ⊗ₜ[R] v)) := by
  rw [← Theta.action_naturality phi x]
  simpa using
    (GeneralLinear.mapScalarExtensionAutomorphisms_apply_scalarExtensionMap
      (V := V) phi (Theta.action A x) (1 ⊗ₜ[R] v))

private noncomputable def evaluatedCoaction (rho : Comodule R H V)
    (A : CommAlgCat.{u} R) (x : points (H := H) A) :
    V →ₗ[R] A ⊗[R] V :=
  (TensorProduct.comm R V A).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id x.ofConv.toLinearMap ∘ₗ rho.coact

private noncomputable def pointActionEnd (rho : Comodule R H V)
    (A : CommAlgCat.{u} R) (x : points (H := H) A) :
    Module.End A (A ⊗[R] V) := by
  let u := evaluatedCoaction rho A x
  exact TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a ↦
        { toFun := fun v ↦ a • u v
          map_add' := fun v w ↦ by simp
          map_smul' := fun r v ↦ by
            rw [u.map_smul]
            exact smul_comm a r (u v) }
      map_add' := fun a b ↦ LinearMap.ext fun v ↦ add_smul a b (u v)
      map_smul' := fun a b ↦ LinearMap.ext fun v ↦ by
        change (a * b) • u v = a • b • u v
        exact (smul_smul a b (u v)).symm }

@[simp]
private theorem pointActionEnd_tmul (rho : Comodule R H V)
    (A : CommAlgCat.{u} R) (x : points (H := H) A) (a : A) (v : V) :
    pointActionEnd rho A x (a ⊗ₜ[R] v) = a • evaluatedCoaction rho A x v :=
  by simp [pointActionEnd]

private theorem evaluatedCoaction_one (rho : Comodule R H V)
    (A : CommAlgCat.{u} R) (v : V) :
    evaluatedCoaction rho A (1 : points (H := H) A) v = 1 ⊗ₜ[R] v := by
  letI : Comodule R H V := rho
  have hmap :
      (TensorProduct.comm R V A).toLinearMap ∘ₗ
          TensorProduct.map LinearMap.id
            ((1 : points (H := H) A).ofConv.toLinearMap) =
        (Algebra.linearMap R A).rTensor V ∘ₗ
          (TensorProduct.comm R V R).toLinearMap ∘ₗ
            Coalgebra.counit.lTensor V := by
    ext m h
    rfl
  rw [evaluatedCoaction, ← LinearMap.comp_assoc, hmap]
  simp only [LinearMap.comp_apply]
  rw [Comodule.lTensor_counit_coact]
  simp

private theorem pointActionEnd_one (rho : Comodule R H V)
    (A : CommAlgCat.{u} R) :
    pointActionEnd rho A (1 : points (H := H) A) = 1 := by
  refine TensorProduct.AlgebraTensorModule.ext fun a v ↦ ?_
  rw [pointActionEnd_tmul, evaluatedCoaction_one]
  exact (TensorProduct.tmul_eq_smul_one_tmul (M := V) a v).symm

private noncomputable def pairedEvaluation (A : CommAlgCat.{u} R)
    (x y : points (H := H) A) :
    V ⊗[R] (H ⊗[R] H) →ₗ[R] A ⊗[R] V :=
  (TensorProduct.comm R V A).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id
      (Algebra.TensorProduct.lift x.ofConv y.ofConv (fun _ _ ↦ .all _ _)).toLinearMap

private theorem pairedEvaluation_comul (rho : Comodule R H V)
    (A : CommAlgCat.{u} R) (x y : points (H := H) A) (v : V) :
    pairedEvaluation A x y
        (Coalgebra.comul.lTensor V (rho.coact v)) =
      evaluatedCoaction rho A (x * y) v := by
  have hmap :
      pairedEvaluation (V := V) A x y ∘ₗ Coalgebra.comul.lTensor V =
        (TensorProduct.comm R V A).toLinearMap ∘ₗ
          TensorProduct.map LinearMap.id (x * y).ofConv.toLinearMap := by
    ext m h
    change
      (Algebra.TensorProduct.lift x.ofConv y.ofConv (fun _ _ ↦ .all _ _)
          (Coalgebra.comul h)) ⊗ₜ[R] m =
        (x * y).ofConv h ⊗ₜ[R] m
    rw [AlgHom.convMul_apply]
  rw [← LinearMap.comp_apply, hmap]
  rfl

private theorem pointActionEnd_evaluatedCoaction (rho : Comodule R H V)
    (A : CommAlgCat.{u} R) (x y : points (H := H) A) (v : V) :
    pointActionEnd rho A x (evaluatedCoaction rho A y v) =
      pairedEvaluation A x y
        (TensorProduct.assoc R V H H (rho.coact.rTensor H (rho.coact v))) := by
  have hmap :
      (pointActionEnd rho A x).restrictScalars R ∘ₗ
          (TensorProduct.comm R V A).toLinearMap ∘ₗ
            TensorProduct.map LinearMap.id y.ofConv.toLinearMap =
        pairedEvaluation (V := V) A x y ∘ₗ
          (TensorProduct.assoc R V H H).toLinearMap ∘ₗ rho.coact.rTensor H := by
    ext m h
    change
      pointActionEnd rho A x (y.ofConv h ⊗ₜ[R] m) =
        pairedEvaluation A x y
          (TensorProduct.assoc R V H H (rho.coact m ⊗ₜ[R] h))
    rw [pointActionEnd_tmul]
    have hz : ∀ z : V ⊗[R] H,
        y.ofConv h •
            (TensorProduct.comm R V A
              (TensorProduct.map LinearMap.id x.ofConv.toLinearMap z)) =
          pairedEvaluation A x y (TensorProduct.assoc R V H H (z ⊗ₜ[R] h)) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp [pairedEvaluation]
      | tmul n k => simp [pairedEvaluation, TensorProduct.smul_tmul', mul_comm]
      | add z w hz hw =>
          simpa only [map_add, smul_add, TensorProduct.add_tmul] using
            congrArg₂ (fun p q ↦ p + q) hz hw
    exact hz (rho.coact m)
  have hv := congrArg (fun f : V ⊗[R] H →ₗ[R] A ⊗[R] V ↦ f (rho.coact v)) hmap
  simp only [LinearMap.comp_apply] at hv
  change
    pointActionEnd rho A x
        (TensorProduct.comm R V A
          (TensorProduct.map LinearMap.id y.ofConv.toLinearMap (rho.coact v))) = _ at hv
  exact hv

private theorem pointActionEnd_mul (rho : Comodule R H V)
    (A : CommAlgCat.{u} R) (x y : points (H := H) A) :
    pointActionEnd rho A (x * y) = pointActionEnd rho A x * pointActionEnd rho A y := by
  letI : Comodule R H V := rho
  refine TensorProduct.AlgebraTensorModule.ext fun a v ↦ ?_
  rw [Module.End.mul_apply, pointActionEnd_tmul, pointActionEnd_tmul, map_smul,
    pointActionEnd_evaluatedCoaction, Comodule.coassoc_apply,
    pairedEvaluation_comul]

private noncomputable def pointActionMonoidHom (rho : Comodule R H V)
    (A : CommAlgCat.{u} R) :
    points (H := H) A →* Module.End A (A ⊗[R] V) where
  toFun := pointActionEnd rho A
  map_one' := pointActionEnd_one rho A
  map_mul' := pointActionEnd_mul rho A

private noncomputable def rawPointAction (rho : Comodule R H V)
    (A : CommAlgCat.{u} R) :
    points (H := H) A ⟶ GeneralLinear.scalarExtensionAutomorphisms (V := V) A :=
  GrpCat.ofHom (pointActionMonoidHom rho A).toHomUnits

@[simp]
private theorem rawPointAction_val (rho : Comodule R H V)
    (A : CommAlgCat.{u} R) (x : points (H := H) A) :
    (rawPointAction rho A x).val = pointActionEnd rho A x :=
  rfl

private theorem evaluatedCoaction_naturality (rho : Comodule R H V)
    {A B : CommAlgCat.{u} R} (phi : A ⟶ B) (x : points (H := H) A) (v : V) :
    GeneralLinear.scalarExtensionMap (V := V) phi (evaluatedCoaction rho A x v) =
      evaluatedCoaction rho B (mapPoints (H := H) phi x) v := by
  have hz : ∀ z : V ⊗[R] H,
      GeneralLinear.scalarExtensionMap (V := V) phi
          (TensorProduct.comm R V A
            (TensorProduct.map LinearMap.id x.ofConv.toLinearMap z)) =
        TensorProduct.comm R V B
          (TensorProduct.map LinearMap.id
            (mapPoints (H := H) phi x).ofConv.toLinearMap z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m h =>
        simp only [TensorProduct.map_tmul, LinearMap.id_apply,
          TensorProduct.comm_tmul, GeneralLinear.scalarExtensionMap_tmul,
          AlgHom.coe_toLinearMap]
        rfl
    | add z w hz hw => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) hz hw
  exact hz (rho.coact v)

private theorem rawPointAction_naturality (rho : Comodule R H V)
    {A B : CommAlgCat.{u} R} (phi : A ⟶ B) (x : points (H := H) A) :
    GeneralLinear.mapScalarExtensionAutomorphisms (V := V) phi (rawPointAction rho A x) =
      rawPointAction rho B (mapPoints (H := H) phi x) := by
  symm
  apply GeneralLinear.eq_mapScalarExtensionAutomorphisms_of_apply_scalarExtensionMap_eq
    (V := V) phi (rawPointAction rho A x)
      (rawPointAction rho B (mapPoints (H := H) phi x))
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
      rw [GeneralLinear.scalarExtensionMap_tmul]
      change
        pointActionEnd rho B (mapPoints (H := H) phi x)
            (phi.hom a ⊗ₜ[R] v) =
          GeneralLinear.scalarExtensionMap (V := V) phi
            (pointActionEnd rho A x (a ⊗ₜ[R] v))
      rw [pointActionEnd_tmul, pointActionEnd_tmul,
        GeneralLinear.scalarExtensionMap_smul, evaluatedCoaction_naturality]
  | add z w hz hw => simp [hz, hw]

/-- The natural point representation induced by a right `H`-comodule structure. -/
noncomputable def ofComodule (rho : Comodule R H V) :
    PointRepresentation (R := R) (H := H) (V := V) where
  app A := rawPointAction rho A ≫
    eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A).symm
  naturality A B phi := by
    change
      mapPoints (H := H) phi ≫ rawPointAction rho B ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) B).symm =
        rawPointAction rho A ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A).symm ≫
          (GeneralLinear.scalarExtensionAutomorphismsFunctor (V := V)).map phi
    rw [GeneralLinear.scalarExtensionAutomorphismsFunctor_map]
    have hraw :
        mapPoints (H := H) phi ≫ rawPointAction rho B =
          rawPointAction rho A ≫
            GeneralLinear.mapScalarExtensionAutomorphisms (V := V) phi := by
      apply GrpCat.ext
      intro x
      exact (rawPointAction_naturality rho phi x).symm
    rw [← Category.assoc, hraw]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

@[simp]
private theorem action_ofComodule (rho : Comodule R H V) (A : CommAlgCat.{u} R) :
    (ofComodule rho).action A = rawPointAction rho A := by
  rw [action, ofComodule]
  change
    (rawPointAction rho A ≫
        eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A).symm) ≫
      eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A) =
        rawPointAction rho A
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The action induced by a coaction, evaluated on a pure tensor. -/
@[simp]
theorem ofComodule_action_tmul (rho : Comodule R H V) (A : CommAlgCat.{u} R)
    (x : points (H := H) A) (a : A) (v : V) :
    ((ofComodule rho).action A x).val (a ⊗ₜ[R] v) =
      a • TensorProduct.comm R V A
        (TensorProduct.map LinearMap.id x.ofConv.toLinearMap (rho.coact v)) := by
  rw [action_ofComodule]
  exact pointActionEnd_tmul rho A x a v

/-- At the universal point, the action induced by a coaction is the flipped coaction. -/
@[simp]
theorem ofComodule_action_universal_one_tmul (rho : Comodule R H V) (v : V) :
    ((ofComodule rho).action (CommAlgCat.of R H) (toConv (AlgHom.id R H))).val
        (1 ⊗ₜ[R] v) =
      TensorProduct.comm R V H (rho.coact v) := by
  rw [ofComodule_action_tmul]
  simp only [one_smul, AlgHom.toLinearMap_id, TensorProduct.map_id,
    LinearMap.id_apply]

private noncomputable def universalGenerator
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    V →ₗ[R] H ⊗[R] V :=
  ((Theta.action (CommAlgCat.of R H) (toConv (AlgHom.id R H))).val.restrictScalars R) ∘ₗ
    TensorProduct.mk R H V 1

private noncomputable def recoveredCoaction
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    V →ₗ[R] V ⊗[R] H :=
  (TensorProduct.comm R H V).toLinearMap ∘ₗ universalGenerator Theta

@[simp]
private theorem universalGenerator_apply
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    universalGenerator Theta v =
      (Theta.action (CommAlgCat.of R H) (toConv (AlgHom.id R H))).val
        (1 ⊗ₜ[R] v) :=
  rfl

@[simp]
private theorem recoveredCoaction_apply
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    recoveredCoaction Theta v = TensorProduct.comm R H V (universalGenerator Theta v) :=
  rfl

private theorem mapPoints_universal {A : Type u} [CommRing A] [Algebra R A]
    (phi : H →ₐ[R] A) :
    mapPoints (H := H) (CommAlgCat.ofHom phi) (toConv (AlgHom.id R H)) =
      toConv phi := by
  apply WithConv.ofConv_injective
  ext h
  rfl

private theorem mapPoints_universal_counit :
    mapPoints (H := H) (CommAlgCat.ofHom (Bialgebra.counitAlgHom R H))
        (toConv (AlgHom.id R H)) = 1 := by
  rw [mapPoints_universal]
  apply WithConv.ofConv_injective
  ext h
  simp only [AlgHom.convOne_apply, Bialgebra.counitAlgHom_apply]
  rfl

private theorem scalarExtensionMap_counit_universalGenerator
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    GeneralLinear.scalarExtensionMap (V := V)
        (CommAlgCat.ofHom (Bialgebra.counitAlgHom R H)) (universalGenerator Theta v) =
      1 ⊗ₜ[R] v := by
  have h := Theta.action_mapPoints_one_tmul
    (CommAlgCat.ofHom (Bialgebra.counitAlgHom R H))
      (toConv (AlgHom.id R H)) v
  rw [mapPoints_universal_counit,
    (Theta.action (CommAlgCat.of R R)).hom.map_one] at h
  simpa only [universalGenerator_apply, Units.val_one, Module.End.one_apply] using h.symm

private theorem recoveredCoaction_counit
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    Coalgebra.counit.lTensor V ∘ₗ recoveredCoaction Theta =
      (TensorProduct.mk R V R).flip 1 := by
  apply LinearMap.ext
  intro v
  apply (TensorProduct.comm R V R).injective
  have hbridge := LinearMap.congr_fun
    (LinearMap.comm_comp_lTensor_comp_comm_eq (Q := V) (Coalgebra.counit (R := R) (A := H)))
      (universalGenerator Theta v)
  simp only [LinearMap.comp_apply] at hbridge
  simp only [LinearMap.comp_apply]
  rw [recoveredCoaction_apply]
  change
    TensorProduct.comm R V R
        (Coalgebra.counit.lTensor V
          (TensorProduct.comm R H V (universalGenerator Theta v))) =
      Coalgebra.counit.rTensor V (universalGenerator Theta v) at hbridge
  rw [hbridge]
  simp only [LinearMap.flip_apply, TensorProduct.mk_apply, TensorProduct.comm_tmul]
  have hmap :
      GeneralLinear.scalarExtensionMap (V := V)
          (CommAlgCat.ofHom (Bialgebra.counitAlgHom R H)) =
        Coalgebra.counit.rTensor V := by
    apply TensorProduct.ext'
    intro h w
    rw [GeneralLinear.scalarExtensionMap_tmul, LinearMap.rTensor_tmul]
    rfl
  rw [← hmap]
  exact scalarExtensionMap_counit_universalGenerator Theta v

private noncomputable abbrev includeLeftAlgHom : H →ₐ[R] H ⊗[R] H :=
  (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := H)).toAlgHom

private noncomputable abbrev includeRightAlgHom : H →ₐ[R] H ⊗[R] H :=
  (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := H)).toAlgHom

private theorem comulPoint_eq_include_mul :
    toConv (Bialgebra.comulAlgHom R H) =
      toConv (includeLeftAlgHom (R := R) (H := H)) *
        toConv (includeRightAlgHom (R := R) (H := H)) := by
  apply WithConv.ofConv_injective
  ext h
  rw [AlgHom.convMul_apply, Bialgebra.comulAlgHom_apply]
  unfold includeLeftAlgHom includeRightAlgHom
  rw [Bialgebra.TensorProduct.includeLeft_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom,
    Algebra.TensorProduct.lift_includeLeft_includeRight]
  rfl

private theorem recoveredCoaction_iterate_eq_include_actions
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    TensorProduct.comm R V (H ⊗[R] H)
        (TensorProduct.assoc R V H H
          ((recoveredCoaction Theta).rTensor H (recoveredCoaction Theta v))) =
      (Theta.action (CommAlgCat.of R (H ⊗[R] H))
          (mapPoints (H := H)
            (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H)))
              (toConv (AlgHom.id R H)))).val
        ((Theta.action (CommAlgCat.of R (H ⊗[R] H))
            (mapPoints (H := H)
              (CommAlgCat.ofHom (includeRightAlgHom (R := R) (H := H)))
                (toConv (AlgHom.id R H)))).val (1 ⊗ₜ[R] v)) := by
  rw [Theta.action_mapPoints_one_tmul
    (CommAlgCat.ofHom (includeRightAlgHom (R := R) (H := H)))
      (toConv (AlgHom.id R H)) v]
  change
    TensorProduct.comm R V (H ⊗[R] H)
        (TensorProduct.assoc R V H H
          ((recoveredCoaction Theta).rTensor H (recoveredCoaction Theta v))) =
      (Theta.action (CommAlgCat.of R (H ⊗[R] H))
          (mapPoints (H := H)
            (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H)))
              (toConv (AlgHom.id R H)))).val
        (GeneralLinear.scalarExtensionMap (V := V)
          (CommAlgCat.ofHom (includeRightAlgHom (R := R) (H := H)))
            (universalGenerator Theta v))
  have hz : ∀ z : H ⊗[R] V,
      TensorProduct.comm R V (H ⊗[R] H)
          (TensorProduct.assoc R V H H
            ((recoveredCoaction Theta).rTensor H (TensorProduct.comm R H V z))) =
        (Theta.action (CommAlgCat.of R (H ⊗[R] H))
            (mapPoints (H := H)
              (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H)))
                (toConv (AlgHom.id R H)))).val
          (GeneralLinear.scalarExtensionMap (V := V)
            (CommAlgCat.ofHom (includeRightAlgHom (R := R) (H := H))) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) hz hw
    | tmul h w =>
        rw [GeneralLinear.scalarExtensionMap_tmul]
        have haction :
            (Theta.action (CommAlgCat.of R (H ⊗[R] H))
                (mapPoints (H := H)
                  (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H)))
                    (toConv (AlgHom.id R H)))).val
              (includeRightAlgHom (R := R) (H := H) h ⊗ₜ[R] w) =
            includeRightAlgHom (R := R) (H := H) h •
              GeneralLinear.scalarExtensionMap (V := V)
                (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H)))
                  (universalGenerator Theta w) := by
          rw [TensorProduct.tmul_eq_smul_one_tmul (M := V), map_smul,
            Theta.action_mapPoints_one_tmul
              (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H)))
                (toConv (AlgHom.id R H)) w]
          rfl
        change
          TensorProduct.comm R V (H ⊗[R] H)
              (TensorProduct.assoc R V H H
                ((recoveredCoaction Theta).rTensor H
                  (TensorProduct.comm R H V (h ⊗ₜ[R] w)))) =
            (Theta.action (CommAlgCat.of R (H ⊗[R] H))
                (mapPoints (H := H)
                  (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H)))
                    (toConv (AlgHom.id R H)))).val
              (includeRightAlgHom (R := R) (H := H) h ⊗ₜ[R] w)
        rw [haction, TensorProduct.comm_tmul, LinearMap.rTensor_tmul,
          recoveredCoaction_apply]
        have hwz : ∀ z : H ⊗[R] V,
            TensorProduct.comm R V (H ⊗[R] H)
                (TensorProduct.assoc R V H H
                  (TensorProduct.comm R H V z ⊗ₜ[R] h)) =
              includeRightAlgHom (R := R) (H := H) h •
                GeneralLinear.scalarExtensionMap (V := V)
                  (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H))) z := by
          intro z
          induction z using TensorProduct.induction_on with
          | zero => simp
          | add z w hz hw =>
              simpa only [map_add, smul_add, TensorProduct.add_tmul] using
                congrArg₂ (fun p q ↦ p + q) hz hw
          | tmul k n =>
              simp only [TensorProduct.comm_tmul, TensorProduct.assoc_tmul]
              rw [GeneralLinear.scalarExtensionMap_tmul]
              change
                (k ⊗ₜ[R] h) ⊗ₜ[R] n =
                  includeRightAlgHom (R := R) (H := H) h •
                    (includeLeftAlgHom (R := R) (H := H) k ⊗ₜ[R] n)
              have hleft : includeLeftAlgHom (R := R) (H := H) k = k ⊗ₜ[R] 1 :=
                Bialgebra.TensorProduct.includeLeft_apply k
              have hright : includeRightAlgHom (R := R) (H := H) h = 1 ⊗ₜ[R] h :=
                Bialgebra.TensorProduct.includeRight_apply h
              rw [hleft, hright, TensorProduct.smul_tmul']
              rw [smul_eq_mul]
              rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        exact hwz (universalGenerator Theta w)
  rw [recoveredCoaction_apply]
  exact hz (universalGenerator Theta v)

private theorem recoveredCoaction_coassoc
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    TensorProduct.assoc R V H H ∘ₗ (recoveredCoaction Theta).rTensor H ∘ₗ
        recoveredCoaction Theta =
      Coalgebra.comul.lTensor V ∘ₗ recoveredCoaction Theta := by
  apply LinearMap.ext
  intro v
  apply (TensorProduct.comm R V (H ⊗[R] H)).injective
  simp only [LinearMap.comp_apply]
  change
    TensorProduct.comm R V (H ⊗[R] H)
        (TensorProduct.assoc R V H H
          ((recoveredCoaction Theta).rTensor H (recoveredCoaction Theta v))) =
      TensorProduct.comm R V (H ⊗[R] H)
        (Coalgebra.comul.lTensor V (recoveredCoaction Theta v))
  rw [recoveredCoaction_iterate_eq_include_actions]
  have hpoint :
      mapPoints (H := H)
          (CommAlgCat.ofHom (Bialgebra.comulAlgHom R H))
            (toConv (AlgHom.id R H)) =
        mapPoints (H := H)
            (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H)))
              (toConv (AlgHom.id R H)) *
          mapPoints (H := H)
            (CommAlgCat.ofHom (includeRightAlgHom (R := R) (H := H)))
              (toConv (AlgHom.id R H)) := by
    rw [mapPoints_universal, mapPoints_universal, mapPoints_universal]
    exact comulPoint_eq_include_mul (R := R) (H := H)
  have haction :
      Theta.action (CommAlgCat.of R (H ⊗[R] H))
          (mapPoints (H := H)
            (CommAlgCat.ofHom (Bialgebra.comulAlgHom R H))
              (toConv (AlgHom.id R H))) =
        Theta.action (CommAlgCat.of R (H ⊗[R] H))
            (mapPoints (H := H)
              (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H)))
                (toConv (AlgHom.id R H))) *
          Theta.action (CommAlgCat.of R (H ⊗[R] H))
            (mapPoints (H := H)
              (CommAlgCat.ofHom (includeRightAlgHom (R := R) (H := H)))
                (toConv (AlgHom.id R H))) := by
    rw [hpoint]
    exact (Theta.action (CommAlgCat.of R (H ⊗[R] H))).hom.map_mul _ _
  have hvalue := congrArg
    (fun g : GeneralLinear.scalarExtensionAutomorphisms (V := V)
        (CommAlgCat.of R (H ⊗[R] H)) ↦ g.val (1 ⊗ₜ[R] v)) haction
  change
    (Theta.action (CommAlgCat.of R (H ⊗[R] H))
        (mapPoints (H := H)
          (CommAlgCat.ofHom (Bialgebra.comulAlgHom R H))
            (toConv (AlgHom.id R H)))).val (1 ⊗ₜ[R] v) =
      (Theta.action (CommAlgCat.of R (H ⊗[R] H))
          (mapPoints (H := H)
            (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H)))
              (toConv (AlgHom.id R H)))).val
        ((Theta.action (CommAlgCat.of R (H ⊗[R] H))
            (mapPoints (H := H)
              (CommAlgCat.ofHom (includeRightAlgHom (R := R) (H := H)))
                (toConv (AlgHom.id R H)))).val (1 ⊗ₜ[R] v)) at hvalue
  have hforward :
      (Theta.action (CommAlgCat.of R (H ⊗[R] H))
          (mapPoints (H := H)
            (CommAlgCat.ofHom (includeLeftAlgHom (R := R) (H := H)))
              (toConv (AlgHom.id R H)))).val
        ((Theta.action (CommAlgCat.of R (H ⊗[R] H))
            (mapPoints (H := H)
              (CommAlgCat.ofHom (includeRightAlgHom (R := R) (H := H)))
                (toConv (AlgHom.id R H)))).val (1 ⊗ₜ[R] v)) =
      GeneralLinear.scalarExtensionMap (V := V)
        (CommAlgCat.ofHom (Bialgebra.comulAlgHom R H)) (universalGenerator Theta v) := by
    rw [← hvalue]
    simpa only [universalGenerator_apply] using
      Theta.action_mapPoints_one_tmul
        (CommAlgCat.ofHom (Bialgebra.comulAlgHom R H))
          (toConv (AlgHom.id R H)) v
  rw [hforward, recoveredCoaction_apply]
  have hbridge := LinearMap.congr_fun
    (LinearMap.comm_comp_lTensor_comp_comm_eq (Q := V) (Coalgebra.comul (R := R) (A := H)))
      (universalGenerator Theta v)
  simp only [LinearMap.comp_apply] at hbridge
  change
    TensorProduct.comm R V (H ⊗[R] H)
        (Coalgebra.comul.lTensor V
          (TensorProduct.comm R H V (universalGenerator Theta v))) =
      Coalgebra.comul.rTensor V (universalGenerator Theta v) at hbridge
  rw [hbridge]
  have hmap :
      GeneralLinear.scalarExtensionMap (V := V)
          (CommAlgCat.ofHom (Bialgebra.comulAlgHom R H)) =
        Coalgebra.comul.rTensor V := by
    apply TensorProduct.ext'
    intro h w
    rw [GeneralLinear.scalarExtensionMap_tmul, LinearMap.rTensor_tmul]
    rfl
  rw [hmap]

/-- Recover a right `H`-comodule structure from a natural point representation by evaluating at
the universal point and flipping the tensor factors. -/
@[instance_reducible] noncomputable def toComodule
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) : Comodule R H V where
  coact := recoveredCoaction Theta
  coassoc := recoveredCoaction_coassoc Theta
  lTensor_counit_comp_coact := recoveredCoaction_counit Theta

private theorem toComodule_coact_apply_private
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    (toComodule Theta).coact v =
      TensorProduct.comm R H V
        ((Theta.action (CommAlgCat.of R H) (toConv (AlgHom.id R H))).val
          (1 ⊗ₜ[R] v)) :=
  rfl

/-- The coaction recovered from a point representation is the flipped universal-point action. -/
@[simp]
theorem toComodule_coact_apply
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) (v : V) :
    (toComodule Theta).coact v =
      TensorProduct.comm R H V
        ((Theta.action (CommAlgCat.of R H) (toConv (AlgHom.id R H))).val
          (1 ⊗ₜ[R] v)) :=
  toComodule_coact_apply_private Theta v

private theorem comodule_ext {rho sigma : Comodule R H V}
    (h : rho.coact = sigma.coact) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

/-- Recovering a comodule from its induced point representation returns the original comodule. -/
@[simp]
theorem toComodule_ofComodule (rho : Comodule R H V) :
    toComodule (ofComodule rho) = rho := by
  apply comodule_ext
  apply LinearMap.ext
  intro v
  rw [toComodule_coact_apply, ofComodule_action_universal_one_tmul]
  exact TensorProduct.comm_comm R H V (rho.coact v)

/-- Reconstructing the point representation from its recovered comodule returns the original
natural action. -/
@[simp]
theorem ofComodule_toComodule
    (Theta : PointRepresentation (R := R) (H := H) (V := V)) :
    ofComodule (toComodule Theta) = Theta := by
  have huniversal :
      (ofComodule (toComodule Theta)).action (CommAlgCat.of R H)
          (toConv (AlgHom.id R H)) =
        Theta.action (CommAlgCat.of R H) (toConv (AlgHom.id R H)) := by
    apply Units.ext
    refine TensorProduct.AlgebraTensorModule.ext fun h v ↦ ?_
    rw [TensorProduct.tmul_eq_smul_one_tmul (M := V), map_smul, map_smul]
    congr 1
    rw [ofComodule_action_universal_one_tmul, toComodule_coact_apply]
    exact TensorProduct.comm_comm R V H
      ((Theta.action (CommAlgCat.of R H) (toConv (AlgHom.id R H))).val
        (1 ⊗ₜ[R] v))
  have haction : ∀ (A : CommAlgCat.{u} R) (x : points (H := H) A),
      (ofComodule (toComodule Theta)).action A x = Theta.action A x := by
    intro A x
    have hforward := (ofComodule (toComodule Theta)).action_naturality
      (CommAlgCat.ofHom x.ofConv) (toConv (AlgHom.id R H))
    have hTheta := Theta.action_naturality
      (CommAlgCat.ofHom x.ofConv) (toConv (AlgHom.id R H))
    rw [mapPoints_universal, toConv_ofConv, huniversal] at hforward
    rw [mapPoints_universal, toConv_ofConv] at hTheta
    exact hforward.symm.trans hTheta
  apply NatTrans.ext
  funext A
  apply (cancel_mono
    (eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V) A))).1
  change
    (ofComodule (toComodule Theta)).action A = Theta.action A
  apply GrpCat.ext
  intro x
  exact haction A x

end PointRepresentation

/-- Natural point representations on `V` are equivalent to right `H`-comodule structures on
`V`. -/
noncomputable def pointRepresentationEquivComodule :
    PointRepresentation (R := R) (H := H) (V := V) ≃ Comodule R H V where
  toFun := PointRepresentation.toComodule
  invFun := PointRepresentation.ofComodule
  left_inv := PointRepresentation.ofComodule_toComodule
  right_inv := PointRepresentation.toComodule_ofComodule

end HopfAlgebra

end TauCeti
