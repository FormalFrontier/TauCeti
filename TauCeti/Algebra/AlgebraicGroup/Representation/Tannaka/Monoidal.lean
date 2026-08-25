/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.PointFaithful
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.ScalarExtension.Monoidal

/-!
# Tensor automorphisms from algebraic-group points

Let `H` be a Hopf algebra over a commutative semiring `R`, and let `A` be a commutative
`R`-algebra. Scalar extension of finite `H`-comodules is a strong monoidal functor

```text
FGComoduleCat R H ⥤ SemimoduleCat A,    M ↦ A ⊗[R] M.
```

Every `A`-valued point of `H` already acts naturally on this functor. This file proves that
the action preserves the tensor product and tensor unit, and therefore packages it as an
automorphism of the corresponding bundled lax monoidal functor. Over a principal ideal domain,
when `H` is free as an `R`-module, this map from points to tensor automorphisms is injective.

Assembling an automorphism of scalar extension from a natural family of linear automorphisms is
`TauCeti.FGComoduleCat.autOfComponents`, which needs only the coalgebra structure; adding the
tensor-unit and tensor comparisons upgrades it to a tensor automorphism here.

This is the faithful direction of the tensor-automorphism formulation of Tannakian
reconstruction. The converse, recovering a point from every tensor automorphism, remains a
separate theorem.

## Main declarations

* `TauCeti.Tannaka.monoidalAutOfComponents`: the same, with the unit and tensor conditions, as a
  tensor automorphism.
* `TauCeti.Tannaka.scalarExtensionComponent`: a tensor-automorphism component transported to an
  explicit scalar-extension tensor product.
* `TauCeti.Tannaka.scalarExtensionComponent_tensor`: the elementwise tensor law for transported
  components.
* `TauCeti.Tannaka.scalarExtensionComponent_one` and
  `TauCeti.Tannaka.scalarExtensionComponent_mul`: transported components are multiplicative in
  the tensor automorphism.
* `TauCeti.Tannaka.scalarExtensionComponentGL`: a transported component as an element of the
  general linear group of the scalar extension.
* `TauCeti.Tannaka.scalarExtensionComponent_tensorUnit` and
  `TauCeti.Tannaka.distribBaseChange_comp_scalarExtensionComponent`: the unit and tensor halves
  of the monoidal condition, read off the transported components.
* `TauCeti.Tannaka.isMonoidal_fgPointNatIsoHom_hom`: point actions on finite comodules preserve the
  tensor unit and tensor product.
* `TauCeti.Tannaka.fgPointTensorIsoHom`: points act on finite-comodule scalar extension by
  tensor automorphisms.
* `TauCeti.Tannaka.fgPointTensorIsoHom_injective`: this action is faithful over a principal
  ideal domain when the Hopf algebra is free.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.5 and 9.4.
* `Mathlib/RepresentationTheory/Tannaka.lean`: the bundled monoidal forgetful functor `forget`,
  point homomorphism `equivHom`, and tensor step in `map_mul_toRightFDRepComp` provide the formal
  pattern adapted here to comodules and scalar extension.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v

section Component

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [Bialgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- The component of a tensor automorphism, transported from the object chosen by the
scalar-extension functor to the explicit tensor product `A ⊗[R] M`. -/
noncomputable def scalarExtensionComponent
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M : FGComoduleCat.{u, v, u} R H) :
    A ⊗[R] M →ₗ[A] A ⊗[R] M :=
  (eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm ≫
    η.hom.hom.app M ≫
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M)).hom

/-- Evaluation formula for a transported tensor-automorphism component. -/
theorem scalarExtensionComponent_apply
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M : FGComoduleCat.{u, v, u} R H) (x : A ⊗[R] M) :
    scalarExtensionComponent R H A η M x =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M)
        (η.hom.hom.app M
          (eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm x)) := by
  rfl

private theorem ofHom_scalarExtensionComponent
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M : FGComoduleCat.{u, v, u} R H)
    (h : (FGComoduleCat.scalarExtensionFunctor R H A).obj M =
      SemimoduleCat.of A (A ⊗[R] M)) :
    SemimoduleCat.ofHom (scalarExtensionComponent R H A η M) =
      eqToHom h.symm ≫
        η.hom.hom.app M ≫
          eqToHom h := by
  cases Subsingleton.elim h (FGComoduleCat.scalarExtensionFunctor_obj R H A M)
  rfl

/-- Tensor automorphisms of scalar extension are equal when all their explicitly transported
components are equal. -/
@[ext]
theorem scalarExtensionComponent_ext
    (η θ : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (h : ∀ M, scalarExtensionComponent R H A η M =
      scalarExtensionComponent R H A θ M) :
    η = θ := by
  apply Aut.ext
  apply LaxMonoidalFunctor.hom_ext
  apply NatTrans.ext
  funext M
  let hM : (FGComoduleCat.scalarExtensionMonoidalFunctor R H A).obj M =
      SemimoduleCat.of A (A ⊗[R] M) :=
    FGComoduleCat.scalarExtensionFunctor_obj R H A M
  have hcomponent := congrArg SemimoduleCat.ofHom (h M)
  rw [ofHom_scalarExtensionComponent R H A η M hM,
    ofHom_scalarExtensionComponent R H A θ M hM] at hcomponent
  have hpre :
      eqToHom hM.symm ≫ η.hom.hom.app M =
        eqToHom hM.symm ≫ θ.hom.hom.app M := by
    apply (cancel_mono (eqToHom hM)).mp
    rw [Category.assoc, Category.assoc]
    exact hcomponent
  exact (cancel_epi (eqToHom hM.symm)).mp hpre

/-- Naturality of the explicitly transported components of a tensor automorphism. -/
theorem scalarExtensionComponent_natural
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    {M N : FGComoduleCat.{u, v, u} R H} (f : M ⟶ N) :
    f.hom.toLinearMap.baseChange A ∘ₗ scalarExtensionComponent R H A η M =
      scalarExtensionComponent R H A η N ∘ₗ f.hom.toLinearMap.baseChange A := by
  let aM : (FGComoduleCat.scalarExtensionFunctor R H A).obj M ⟶
      (FGComoduleCat.scalarExtensionFunctor R H A).obj M :=
    η.hom.hom.app M
  let aN : (FGComoduleCat.scalarExtensionFunctor R H A).obj N ⟶
      (FGComoduleCat.scalarExtensionFunctor R H A).obj N :=
    η.hom.hom.app N
  have hnat :
      (FGComoduleCat.scalarExtensionFunctor R H A).map f ≫ aN =
        aM ≫ (FGComoduleCat.scalarExtensionFunctor R H A).map f :=
    η.hom.hom.naturality f
  let hM := FGComoduleCat.scalarExtensionFunctor_obj R H A M
  let hN := FGComoduleCat.scalarExtensionFunctor_obj R H A N
  let iM := eqToIso hM
  let iN := eqToIso hN
  let bmap := SemimoduleCat.ofHom (f.hom.toLinearMap.baseChange A)
  have hfmap :
      (FGComoduleCat.scalarExtensionFunctor R H A).map f =
        iM.hom ≫ bmap ≫ iN.inv := by
    simpa only [hM, hN, iM, iN, bmap, eqToIso.hom, eqToIso.inv] using
      FGComoduleCat.scalarExtensionFunctor_map R H A f
  rw [hfmap] at hnat
  have hcat :
      (iM.inv ≫ aM ≫ iM.hom) ≫ bmap =
        bmap ≫ (iN.inv ≫ aN ≫ iN.hom) := by
    rw [← cancel_epi iM.hom]
    rw [← cancel_mono iN.inv]
    slice_lhs 1 2 => rw [iM.hom_inv_id]
    slice_rhs 4 6 => rw [iN.hom_inv_id, Category.comp_id]
    simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hnat.symm
  have hcat' :
      SemimoduleCat.ofHom (scalarExtensionComponent R H A η M) ≫ bmap =
        bmap ≫ SemimoduleCat.ofHom (scalarExtensionComponent R H A η N) := by
    rw [ofHom_scalarExtensionComponent R H A η M hM,
      ofHom_scalarExtensionComponent R H A η N hN]
    convert hcat using 1 <;>
      simp only [iM, iN, aM, aN, eqToIso.inv, eqToIso.hom] <;> rfl
  simpa only [bmap, SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom] using
    congrArg SemimoduleCat.Hom.hom hcat'

/-- Tensor compatibility of the explicitly transported components of a tensor automorphism. -/
@[simp]
theorem scalarExtensionComponent_tensor
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M N : FGComoduleCat.{u, v, u} R H) (x : A ⊗[R] M) (y : A ⊗[R] N) :
    scalarExtensionComponent R H A η (M ⊗ N : FGComoduleCat R H)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm
          (x ⊗ₜ[A] y)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm
        (scalarExtensionComponent R H A η M x ⊗ₜ[A]
          scalarExtensionComponent R H A η N y) := by
  let aM : (FGComoduleCat.scalarExtensionFunctor R H A).obj M ⟶
      (FGComoduleCat.scalarExtensionFunctor R H A).obj M :=
    η.hom.hom.app M
  let aN : (FGComoduleCat.scalarExtensionFunctor R H A).obj N ⟶
      (FGComoduleCat.scalarExtensionFunctor R H A).obj N :=
    η.hom.hom.app N
  let aMN : (FGComoduleCat.scalarExtensionFunctor R H A).obj
      (M ⊗ N : FGComoduleCat R H) ⟶
      (FGComoduleCat.scalarExtensionFunctor R H A).obj
        (M ⊗ N : FGComoduleCat R H) :=
    η.hom.hom.app (M ⊗ N : FGComoduleCat R H)
  -- First unpack the bundled monoidal axiom into the tensor-component square.
  have htensor :
      Functor.LaxMonoidal.μ (FGComoduleCat.scalarExtensionFunctor R H A) M N ≫ aMN =
        (aM ⊗ₘ aN) ≫
          Functor.LaxMonoidal.μ (FGComoduleCat.scalarExtensionFunctor R H A) M N :=
    NatTrans.IsMonoidal.tensor (τ := η.hom.hom) M N
  rw [FGComoduleCat.scalarExtensionFunctor_μ] at htensor
  let hM := FGComoduleCat.scalarExtensionFunctor_obj R H A M
  let hN := FGComoduleCat.scalarExtensionFunctor_obj R H A N
  let hMN := FGComoduleCat.scalarExtensionFunctor_obj R H A
    (M ⊗ N : FGComoduleCat R H)
  let iM := eqToIso hM
  let iN := eqToIso hN
  let iMN := eqToIso hMN
  let d :
      (SemimoduleCat.of A (A ⊗[R] M) ⊗ SemimoduleCat.of A (A ⊗[R] N)) ⟶
        SemimoduleCat.of A (A ⊗[R] (M ⊗[R] N)) :=
    SemimoduleCat.ofHom
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap
  have hmon :
      (((iM.hom ⊗ₘ iN.hom) ≫ d ≫ iMN.inv) ≫ aMN) =
        (aM ⊗ₘ aN) ≫ ((iM.hom ⊗ₘ iN.hom) ≫ d ≫ iMN.inv) := by
    simpa only [iM, iN, iMN, d, eqToIso.hom, eqToIso.inv] using htensor
  -- Next cancel the object transports, leaving only explicit scalar-extension components.
  have he :
      (iM.hom ⊗ₘ iN.hom) ≫
          ((iM.inv ≫ aM ≫ iM.hom) ⊗ₘ (iN.inv ≫ aN ≫ iN.hom)) =
        ((aM ≫ iM.hom) ⊗ₘ (aN ≫ iN.hom)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Iso.hom_inv_id_assoc]
  have he' :
      (aM ⊗ₘ aN) ≫ (iM.hom ⊗ₘ iN.hom) =
        ((aM ≫ iM.hom) ⊗ₘ (aN ≫ iN.hom)) :=
    MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
  have hcat :
      d ≫ (iMN.inv ≫ aMN ≫ iMN.hom) =
        ((iM.inv ≫ aM ≫ iM.hom) ⊗ₘ (iN.inv ≫ aN ≫ iN.hom)) ≫ d := by
    rw [← cancel_epi (iM.hom ⊗ₘ iN.hom)]
    rw [← cancel_mono iMN.inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    conv_rhs => rw [← Category.assoc]
    rw [he, ← he']
    simpa only [Category.assoc] using hmon
  -- Use the same bridge to replace all three transported maps before passing to linear maps.
  have hcat' :
      d ≫ SemimoduleCat.ofHom
          (scalarExtensionComponent R H A η (M ⊗ N : FGComoduleCat R H)) =
        (SemimoduleCat.ofHom (scalarExtensionComponent R H A η M) ⊗ₘ
          SemimoduleCat.ofHom (scalarExtensionComponent R H A η N)) ≫ d := by
    rw [ofHom_scalarExtensionComponent R H A η (M ⊗ N : FGComoduleCat R H) hMN,
      ofHom_scalarExtensionComponent R H A η M hM,
      ofHom_scalarExtensionComponent R H A η N hN]
    convert hcat using 1 <;>
      simp only [iM, iN, iMN, aM, aN, aMN, eqToIso.inv, eqToIso.hom] <;> rfl
  have hlin := congrArg SemimoduleCat.Hom.hom hcat'
  simp only [SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom] at hlin
  rw [SemimoduleCat.hom_tensorHom] at hlin
  -- Finally evaluate the linear-map equality on a pure tensor.
  have happ := LinearMap.congr_fun hlin (x ⊗ₜ[A] y)
  -- No carrier-level rewrite theorem unfolds these two categorical applications, so display
  -- their underlying linear maps before evaluating `TensorProduct.map`.
  change scalarExtensionComponent R H A η (M ⊗ N : FGComoduleCat R H)
      (d.hom (x ⊗ₜ[A] y)) =
    d.hom (TensorProduct.map (scalarExtensionComponent R H A η M)
      (scalarExtensionComponent R H A η N) (x ⊗ₜ[A] y)) at happ
  rw [TensorProduct.map_tmul] at happ
  change scalarExtensionComponent R H A η (M ⊗ N : FGComoduleCat R H)
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm
        (x ⊗ₜ[A] y)) =
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm
      (scalarExtensionComponent R H A η M x ⊗ₜ[A]
        scalarExtensionComponent R H A η N y) at happ
  exact happ

-- Conjugating by an object transport turns the identity into the identity. Stated for a
-- variable object so that the transport can be substituted away.
private theorem eqToHom_conj_id {C : Type*} [Category C] {X Y : C} (h : X = Y) :
    eqToHom h.symm ≫ 𝟙 X ≫ eqToHom h = 𝟙 Y := by
  subst h
  simp

-- Conjugating by an object transport turns composition into composition: the inner transports
-- cancel. Stated for a variable object so that the transport can be substituted away.
private theorem eqToHom_conj_comp {C : Type*} [Category C] {X Y : C} (h : X = Y) (a b : X ⟶ X) :
    (eqToHom h.symm ≫ a ≫ eqToHom h) ≫ (eqToHom h.symm ≫ b ≫ eqToHom h) =
      eqToHom h.symm ≫ (a ≫ b) ≫ eqToHom h := by
  subst h
  simp

/-- The identity tensor automorphism has identity transported components. -/
@[simp]
theorem scalarExtensionComponent_one (M : FGComoduleCat.{u, v, u} R H) :
    scalarExtensionComponent R H A
        (1 : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) M =
      LinearMap.id := by
  have h : SemimoduleCat.ofHom
      (scalarExtensionComponent R H A
        (1 : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) M) =
      SemimoduleCat.ofHom (LinearMap.id : A ⊗[R] M →ₗ[A] A ⊗[R] M) := by
    rw [ofHom_scalarExtensionComponent R H A _ M
      (FGComoduleCat.scalarExtensionFunctor_obj R H A M)]
    exact eqToHom_conj_id (FGComoduleCat.scalarExtensionFunctor_obj R H A M)
  simpa only [SemimoduleCat.hom_ofHom] using congrArg SemimoduleCat.Hom.hom h

/-- Multiplying tensor automorphisms composes their transported components: multiplication in
`Aut` is reverse composition, and the object transports between the two components cancel. -/
@[simp]
theorem scalarExtensionComponent_mul
    (η θ : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M : FGComoduleCat.{u, v, u} R H) :
    scalarExtensionComponent R H A (η * θ) M =
      scalarExtensionComponent R H A η M ∘ₗ scalarExtensionComponent R H A θ M := by
  have hM := FGComoduleCat.scalarExtensionFunctor_obj R H A M
  have h : SemimoduleCat.ofHom (scalarExtensionComponent R H A (η * θ) M) =
      SemimoduleCat.ofHom (scalarExtensionComponent R H A θ M) ≫
        SemimoduleCat.ofHom (scalarExtensionComponent R H A η M) := by
    rw [ofHom_scalarExtensionComponent R H A (η * θ) M hM,
      ofHom_scalarExtensionComponent R H A η M hM,
      ofHom_scalarExtensionComponent R H A θ M hM]
    exact (eqToHom_conj_comp hM (θ.hom.hom.app M) (η.hom.hom.app M)).symm
  simpa only [SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom] using
    congrArg SemimoduleCat.Hom.hom h

/-- The transported component of a tensor automorphism, as an element of the general linear
group of the scalar extension. Its inverse is the component of the inverse automorphism. -/
noncomputable def scalarExtensionComponentGL
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M : FGComoduleCat.{u, v, u} R H) :
    LinearMap.GeneralLinearGroup A (A ⊗[R] M) where
  val := scalarExtensionComponent R H A η M
  inv := scalarExtensionComponent R H A η⁻¹ M
  val_inv := by
    rw [Module.End.mul_eq_comp, ← scalarExtensionComponent_mul, mul_inv_cancel,
      scalarExtensionComponent_one, Module.End.one_eq_id]
  inv_val := by
    rw [Module.End.mul_eq_comp, ← scalarExtensionComponent_mul, inv_mul_cancel,
      scalarExtensionComponent_one, Module.End.one_eq_id]

/-- The underlying linear map of the general-linear-group form of a transported component is
that component. -/
@[simp]
theorem scalarExtensionComponentGL_coe
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M : FGComoduleCat.{u, v, u} R H) :
    (scalarExtensionComponentGL R H A η M : Module.End A (A ⊗[R] M)) =
      scalarExtensionComponent R H A η M := by
  simp [scalarExtensionComponentGL]

/-- The inverse of a transported component is the transported component of the inverse tensor
automorphism. -/
@[simp]
theorem scalarExtensionComponentGL_inv
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M : FGComoduleCat.{u, v, u} R H) :
    (scalarExtensionComponentGL R H A η M)⁻¹ =
      scalarExtensionComponentGL R H A η⁻¹ M := by
  apply Units.ext
  rfl

/-- The transported component of a tensor automorphism at the tensor unit is the identity:
this is the unit half of the monoidal condition. -/
@[simp]
theorem scalarExtensionComponent_tensorUnit
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :
    scalarExtensionComponent R H A η (𝟙_ (FGComoduleCat R H)) = LinearMap.id := by
  -- The unit comparison of a strong monoidal functor is an isomorphism, so the monoidal
  -- condition at the tensor unit cancels down to the identity component. The condition is
  -- restated at the underlying functor, where the monoidal structure is the discoverable one.
  have hunit : Functor.LaxMonoidal.ε (FGComoduleCat.scalarExtensionFunctor R H A) ≫
      η.hom.hom.app (𝟙_ (FGComoduleCat R H)) =
      Functor.LaxMonoidal.ε (FGComoduleCat.scalarExtensionFunctor R H A) :=
    NatTrans.IsMonoidal.unit (τ := η.hom.hom)
  have happ : η.hom.hom.app (𝟙_ (FGComoduleCat R H)) =
      𝟙 ((FGComoduleCat.scalarExtensionFunctor R H A).obj (𝟙_ (FGComoduleCat R H))) :=
    (cancel_epi (Functor.LaxMonoidal.ε (FGComoduleCat.scalarExtensionFunctor R H A))).mp
      (hunit.trans (Category.comp_id _).symm)
  have h : SemimoduleCat.ofHom
      (scalarExtensionComponent R H A η (𝟙_ (FGComoduleCat R H))) =
      SemimoduleCat.ofHom (LinearMap.id :
        A ⊗[R] (𝟙_ (FGComoduleCat R H)) →ₗ[A] A ⊗[R] (𝟙_ (FGComoduleCat R H))) := by
    rw [ofHom_scalarExtensionComponent R H A η _
      (FGComoduleCat.scalarExtensionFunctor_obj R H A (𝟙_ (FGComoduleCat R H))), happ]
    exact eqToHom_conj_id
      (FGComoduleCat.scalarExtensionFunctor_obj R H A (𝟙_ (FGComoduleCat R H)))
  simpa only [SemimoduleCat.hom_ofHom] using congrArg SemimoduleCat.Hom.hom h

/-- Composite form of the tensor law for transported components: the scalar-extension
tensorator intertwines the components at `M` and `N` with the component at `M ⊗ N`. -/
theorem distribBaseChange_comp_scalarExtensionComponent
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M N : FGComoduleCat.{u, v, u} R H) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap ∘ₗ
        TensorProduct.map (scalarExtensionComponent R H A η M)
          (scalarExtensionComponent R H A η N) =
      scalarExtensionComponent R H A η (M ⊗ N : FGComoduleCat R H) ∘ₗ
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro x y
  simpa only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe] using (scalarExtensionComponent_tensor R H A η M N x y).symm

/-- Evaluate a transported scalar-extension component from the corresponding natural
transformation component. -/
theorem scalarExtensionComponent_eq_of_hom_app
    (M : FGComoduleCat.{u, v, u} R H)
    (F : LinearMap.GeneralLinearGroup A (A ⊗[R] M))
    (eta : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (happ : eta.hom.hom.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M) ≫
        F.toLinearEquiv.toModuleIsoₛ.hom ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm) :
    scalarExtensionComponent R H A eta M = (F : Module.End A (A ⊗[R] M)) := by
  apply LinearMap.ext
  intro x
  rw [scalarExtensionComponent_apply, happ]
  let hM := FGComoduleCat.scalarExtensionFunctor_obj R H A M
  -- The functor object is definitionally the explicit scalar extension, but this equality is
  -- hidden by the categorical and linear-map wrappers. Displaying the four transports lets the
  -- standard `eqToHom` simp lemmas cancel them without unfolding either public construction.
  change (eqToHom hM.symm ≫
      (eqToHom hM ≫ F.toLinearEquiv.toModuleIsoₛ.hom ≫ eqToHom hM.symm) ≫
        eqToHom hM) x = _
  simp

/-- A natural automorphism of scalar extension is monoidal when its transported linear
components preserve the tensor unit and tensor products. -/
theorem isMonoidal_of_linear_components
    (F : ∀ M : FGComoduleCat.{u, v, u} R H,
      LinearMap.GeneralLinearGroup A (A ⊗[R] M))
    (η : Aut (FGComoduleCat.scalarExtensionFunctor R H A))
    (happ : ∀ M : FGComoduleCat.{u, v, u} R H,
      η.hom.app M =
        eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M) ≫
          (F M).toLinearEquiv.toModuleIsoₛ.hom ≫
            eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm)
    (hunit : F (𝟙_ (FGComoduleCat R H)) = 1)
    (htensor : ∀ M N : FGComoduleCat.{u, v, u} R H,
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap.comp
          (TensorProduct.map (F M : Module.End A (A ⊗[R] M))
            (F N : Module.End A (A ⊗[R] N))) =
        (F (M ⊗ N : FGComoduleCat R H) :
          Module.End A (A ⊗[R] ((M ⊗ N : FGComoduleCat R H) : Type u))).comp
            (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap) :
    NatTrans.IsMonoidal η.hom := by
  constructor
  · rw [FGComoduleCat.scalarExtensionFunctor_ε, happ]
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro a
    simp only [Category.assoc, SemimoduleCat.comp_apply,
      LinearEquiv.toModuleIsoₛ_hom]
    rw [hunit]
    simp
  · intro M N
    -- The ascribed categorical type is load-bearing: `congrArg` on its own yields the
    -- definitionally equal `LinearMap.comp`/`TensorProduct.map` spelling, which `erw` matches
    -- syntactically and so would not find.
    have htensor_cat :
        SemimoduleCat.ofHom
              (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap ≫
            SemimoduleCat.ofHom
              (F (M ⊗ N : FGComoduleCat R H) :
                Module.End A (A ⊗[R] ((M ⊗ N : FGComoduleCat R H) : Type u))) =
          (SemimoduleCat.ofHom
                (F M : Module.End A (A ⊗[R] M)) ⊗ₘ
              SemimoduleCat.ofHom
                (F N : Module.End A (A ⊗[R] N))) ≫
            SemimoduleCat.ofHom
              (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap :=
      congrArg SemimoduleCat.ofHom (htensor M N).symm
    erw [FGComoduleCat.scalarExtensionFunctor_μ,
      happ, happ, happ]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [cancel_epi]
    erw [Category.assoc, eqToHom_trans_assoc]
    simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc, eqToHom_trans,
      eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.toModuleIsoₛ_hom]
    erw [← Category.assoc, htensor_cat, Category.assoc]

/-- A family of `A`-linear automorphisms of the scalar extensions of the finite comodules that is
natural in the comodule, preserves the tensor unit, and is compatible with the tensor comparison,
as a tensor automorphism of scalar extension. -/
noncomputable def monoidalAutOfComponents
    (F : ∀ M : FGComoduleCat.{u, v, u} R H, LinearMap.GeneralLinearGroup A (A ⊗[R] M))
    (hnat : ∀ {M N : FGComoduleCat.{u, v, u} R H} (g : M ⟶ N),
      g.hom.toLinearMap.baseChange A ∘ₗ (F M : Module.End A (A ⊗[R] M)) =
        (F N : Module.End A (A ⊗[R] N)) ∘ₗ g.hom.toLinearMap.baseChange A)
    (hunit : F (𝟙_ (FGComoduleCat R H)) = 1)
    (htensor : ∀ M N : FGComoduleCat.{u, v, u} R H,
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap.comp
          (TensorProduct.map (F M : Module.End A (A ⊗[R] M))
            (F N : Module.End A (A ⊗[R] N))) =
        (F (M ⊗ N : FGComoduleCat R H) :
          Module.End A (A ⊗[R] ((M ⊗ N : FGComoduleCat R H) : Type u))).comp
            (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap) :
    Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A) :=
  @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _ (FGComoduleCat.autOfComponents R H A F hnat)
    (isMonoidal_of_linear_components R H A F (FGComoduleCat.autOfComponents R H A F hnat)
      (FGComoduleCat.autOfComponents_hom_app R H A F hnat) hunit htensor)

/-- The transported component of the tensor automorphism assembled from a natural monoidal family
of linear automorphisms is that family. -/
@[simp]
theorem scalarExtensionComponent_monoidalAutOfComponents
    (F : ∀ M : FGComoduleCat.{u, v, u} R H, LinearMap.GeneralLinearGroup A (A ⊗[R] M))
    (hnat : ∀ {M N : FGComoduleCat.{u, v, u} R H} (g : M ⟶ N),
      g.hom.toLinearMap.baseChange A ∘ₗ (F M : Module.End A (A ⊗[R] M)) =
        (F N : Module.End A (A ⊗[R] N)) ∘ₗ g.hom.toLinearMap.baseChange A)
    (hunit : F (𝟙_ (FGComoduleCat R H)) = 1)
    (htensor : ∀ M N : FGComoduleCat.{u, v, u} R H,
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap.comp
          (TensorProduct.map (F M : Module.End A (A ⊗[R] M))
            (F N : Module.End A (A ⊗[R] N))) =
        (F (M ⊗ N : FGComoduleCat R H) :
          Module.End A (A ⊗[R] ((M ⊗ N : FGComoduleCat R H) : Type u))).comp
            (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap)
    (M : FGComoduleCat.{u, v, u} R H) :
    scalarExtensionComponent R H A (monoidalAutOfComponents R H A F hnat hunit htensor) M =
      (F M : Module.End A (A ⊗[R] M)) :=
  scalarExtensionComponent_eq_of_hom_app R H A M (F M) _
    (FGComoduleCat.autOfComponents_hom_app R H A F hnat M)
end Component

section Generic

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [HopfAlgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

open Functor.LaxMonoidal

/-- The point action on the tensor unit is the identity automorphism. -/
@[simp]
theorem ofLinearEquiv_pointsAction_tensorUnit_eq_one
    (g : WithConv (H →ₐ[R] A)) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Comodule.pointsAction (𝟙_ (FGComoduleCat R H)) g) = 1 := by
  apply Units.ext
  -- `Units.ext` still hides the values of `ofLinearEquiv` and `1` behind unit and equivalence
  -- wrappers, so expose their definitionally equal underlying linear maps before rewriting.
  change (Comodule.pointsAction (𝟙_ (FGComoduleCat R H)) g :
    A ⊗[R] (𝟙_ (FGComoduleCat R H)) →ₗ[A] A ⊗[R] (𝟙_ (FGComoduleCat R H))) =
      LinearMap.id
  rw [Comodule.pointsAction_toLinearMap, Comodule.endOfPoint_trivial]

/-- The scalar-extension tensorator intertwines the tensor product of two point actions with the
point action on the tensor product comodule. -/
theorem distribBaseChange_comp_pointsAction
    (g : WithConv (H →ₐ[R] A)) (M N : FGComoduleCat.{u, v, u} R H) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap.comp
        (TensorProduct.map
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) :
            Module.End A (A ⊗[R] M))
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g) :
            Module.End A (A ⊗[R] N))) =
      (LinearMap.GeneralLinearGroup.ofLinearEquiv
          (Comodule.pointsAction (M ⊗ N : FGComoduleCat R H) g) :
        Module.End A (A ⊗[R] ((M ⊗ N : FGComoduleCat R H) : Type u))).comp
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap := by
  have hpoint (P : FGComoduleCat.{u, v, u} R H) :
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction P g) :
        Module.End A (A ⊗[R] P)) = Comodule.endOfPoint P g.ofConv :=
    Comodule.pointsAction_toLinearMap P g
  rw [hpoint M, hpoint N, hpoint (M ⊗ N : FGComoduleCat R H)]
  exact Comodule.endOfPoint_tensor g.ofConv

/-- The natural automorphism induced by an algebra-valued point is monoidal. -/
theorem isMonoidal_fgPointNatIsoHom_hom (g : WithConv (H →ₐ[R] A)) :
    NatTrans.IsMonoidal (fgPointNatIsoHom R H A g).hom := by
  apply isMonoidal_of_linear_components R H A
    (fun M ↦ LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
  · exact fgPointNatIsoHom_hom_app R H A g
  · exact ofLinearEquiv_pointsAction_tensorUnit_eq_one R H A g
  · exact distribBaseChange_comp_pointsAction R H A g

/-- An algebra-valued point as a tensor automorphism of finite-comodule scalar extension. -/
@[expose] noncomputable def fgPointTensorIso (g : WithConv (H →ₐ[R] A)) :
    FGComoduleCat.scalarExtensionMonoidalFunctor R H A ≅
      FGComoduleCat.scalarExtensionMonoidalFunctor R H A := by
  exact @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _
    (fgPointNatIsoHom R H A g) (isMonoidal_fgPointNatIsoHom_hom R H A g)

/-- Forgetting tensor compatibility from the point automorphism recovers its underlying natural
automorphism. -/
@[simp]
theorem fgPointTensorIso_hom_hom (g : WithConv (H →ₐ[R] A)) :
    (fgPointTensorIso R H A g).hom.hom = (fgPointNatIsoHom R H A g).hom :=
  (rfl)

/-- The transported component of the tensor automorphism induced by a point is the usual point
action on every finite comodule. -/
@[simp]
theorem scalarExtensionComponent_fgPointTensorIso
    (g : WithConv (H →ₐ[R] A)) (M : FGComoduleCat.{u, v, u} R H) :
    scalarExtensionComponent R H A (fgPointTensorIso R H A g) M =
      (Comodule.pointsAction M g).toLinearMap := by
  have h := scalarExtensionComponent_eq_of_hom_app R H A M
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
    (fgPointTensorIso R H A g) (by
      rw [fgPointTensorIso_hom_hom]
      exact fgPointNatIsoHom_hom_app R H A g M)
  exact h

/-- Forgetting tensor compatibility from the inverse point automorphism recovers the inverse
underlying natural automorphism. -/
@[simp]
theorem fgPointTensorIso_inv_hom (g : WithConv (H →ₐ[R] A)) :
    (fgPointTensorIso R H A g).inv.hom = (fgPointNatIsoHom R H A g).inv :=
  rfl

/-- Algebra-valued points act on finite-comodule scalar extension by tensor automorphisms. -/
@[expose] noncomputable def fgPointTensorIsoHom :
    WithConv (H →ₐ[R] A) →*
      Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A) where
  toFun := fgPointTensorIso R H A
  map_one' := by
    apply Aut.ext
    apply LaxMonoidalFunctor.hom_ext
    refine (fgPointTensorIso_hom_hom R H A 1).trans ?_
    exact (congrArg Iso.hom (map_one (fgPointNatIsoHom R H A))).trans (by rfl)
  map_mul' g h := by
    apply Aut.ext
    apply LaxMonoidalFunctor.hom_ext
    refine (fgPointTensorIso_hom_hom R H A (g * h)).trans ?_
    exact (congrArg Iso.hom (map_mul (fgPointNatIsoHom R H A) g h)).trans (by rfl)

/-- Evaluating the point tensor-action homomorphism gives the corresponding tensor
automorphism. -/
@[simp]
theorem fgPointTensorIsoHom_apply (g : WithConv (H →ₐ[R] A)) :
    fgPointTensorIsoHom R H A g = fgPointTensorIso R H A g :=
  rfl

end Generic

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (H : Type u) [Semiring H] [HopfAlgebra R H] [Module.Free R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- The tensor-automorphism action of points is faithful over a principal ideal domain when the
Hopf algebra is free as a module. -/
theorem fgPointTensorIsoHom_injective :
    Function.Injective (fgPointTensorIsoHom R H A) := by
  intro g h hgh
  apply fgPointNatIsoHom_injective R H A
  apply Iso.ext
  apply NatTrans.ext
  funext (M : FGComoduleCat.{u, u, u} R H)
  have hhom := congrArg LaxMonoidalFunctor.Hom.hom (congrArg Iso.hom hgh)
  simp only [fgPointTensorIsoHom_apply, fgPointTensorIso_hom_hom] at hhom
  exact congrArg (fun η ↦ η.app M) hhom

end

end TauCeti.Tannaka
