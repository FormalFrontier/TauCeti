/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

This is the faithful direction of the tensor-automorphism formulation of Tannakian
reconstruction. The converse, recovering a point from every tensor automorphism, remains a
separate theorem.

## Main declarations

* `TauCeti.Tannaka.scalarExtensionComponent`: a tensor-automorphism component transported to an
  explicit scalar-extension tensor product.
* `TauCeti.Tannaka.scalarExtensionComponent_tensor`: the elementwise tensor law for transported
  components.
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

end Component

section Generic

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [HopfAlgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

open Functor.LaxMonoidal

/-- The natural automorphism induced by an algebra-valued point is monoidal. -/
theorem isMonoidal_fgPointNatIsoHom_hom (g : WithConv (H →ₐ[R] A)) :
    NatTrans.IsMonoidal (fgPointNatIsoHom R H A g).hom := by
  constructor
  · rw [FGComoduleCat.scalarExtensionFunctor_ε, fgPointNatIsoHom_hom_app]
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro a
    simp [Comodule.pointsAction_toLinearMap, Comodule.endOfPoint_trivial]
  · intro M N
    let _ : Comodule R H (M ⊗[R] N) :=
      inferInstanceAs (Comodule R H ((M ⊗ N : FGComoduleCat R H) : Type u))
    have htensor :
            SemimoduleCat.ofHom
              (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap ≫
            SemimoduleCat.ofHom (Comodule.endOfPoint
              ((M ⊗ N : FGComoduleCat R H) : Type u) g.ofConv) =
          (SemimoduleCat.ofHom (Comodule.endOfPoint M g.ofConv) ⊗ₘ
              SemimoduleCat.ofHom (Comodule.endOfPoint N g.ofConv)) ≫
            SemimoduleCat.ofHom
              (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap := by
      apply SemimoduleCat.hom_ext
      exact (Comodule.endOfPoint_tensor_of_coact_eq (R := R) (H := H) (A := A)
        (V := M) (W := N) (FGComoduleCat.tensor_coact (R := R) (C := H) M N)
          g.ofConv).symm
    erw [FGComoduleCat.scalarExtensionFunctor_μ,
      fgPointNatIsoHom_hom_app, fgPointNatIsoHom_hom_app,
      fgPointNatIsoHom_hom_app]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [cancel_epi]
    erw [Category.assoc, eqToHom_trans_assoc]
    simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc, eqToHom_trans,
      eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.toModuleIsoₛ_hom,
      Comodule.pointsAction_toLinearMap]
    erw [← Category.assoc, htensor, Category.assoc]

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
  apply LinearMap.ext
  intro x
  unfold scalarExtensionComponent
  rw [fgPointTensorIso_hom_hom, fgPointNatIsoHom_hom_app]
  let hM := FGComoduleCat.scalarExtensionFunctor_obj R H A M
  -- After rewriting the point-induced component, only transport along `hM` remains; displaying
  -- the four `eqToHom`s lets the category simp lemmas cancel this object equality.
  change (eqToHom hM.symm ≫
      (eqToHom hM ≫ (Comodule.pointsAction M g).toModuleIsoₛ.hom ≫
        eqToHom hM.symm) ≫ eqToHom hM) x = _
  simp

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
