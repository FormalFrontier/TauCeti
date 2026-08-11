/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ScalarExtension
public import TauCeti.LinearAlgebra.JordanChevalley.Functoriality

/-!
# Jordan factors of point actions

Let `H` be a Hopf algebra over a field `k`, let `K` be a perfect extension field, and let
`g : H →ₐ[k] K` be a `K`-valued point. On every finite-dimensional `H`-comodule, `g` acts
by a linear automorphism after scalar extension to `K`. This file packages the semisimple and
unipotent factors of those automorphisms as natural automorphisms of the finite-comodule scalar
extension functor.

Naturality is substantive: a comodule morphism need be neither injective nor surjective. It follows
from functoriality of the multiplicative Jordan--Chevalley decomposition under arbitrary
intertwiners. The two natural factors commute componentwise and their product recovers the original
point action.

Tensor compatibility is a separate downstream step. Once the factors are tensor automorphisms,
Tannakian reconstruction can lift them from compatible actions on representations to points of the
original affine group. This is the representation-theoretic bridge in Layer 4 of the
ReductiveGroups roadmap.

## Main declarations

* `TauCeti.Tannaka.semisimplePointNatIso`: the natural semisimple factor of a point action.
* `TauCeti.Tannaka.unipotentPointNatIso`: the natural unipotent factor of a point action.
* `TauCeti.Tannaka.unipotentPointNatIso_hom_comp_semisimplePointNatIso_hom`: their product is the
  original point action.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v w x

variable (k : Type u) (H : Type v) (K : Type x) [Field k] [Semiring H] [HopfAlgebra k H]
  [Field K] [Algebra k K] [PerfectField K]

private noncomputable def semisimplePointIso (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, v, w} k H) :
    (FGComoduleCat.scalarExtensionFunctor k H K).obj M ≅
      (FGComoduleCat.scalarExtensionFunctor k H K).obj M :=
  (eqToIso (FGComoduleCat.scalarExtensionFunctor_obj k H K M)).trans
    (((GeneralLinearGroup.semisimplePart (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (Comodule.pointsAction M g))).toLinearEquiv.toModuleIsoₛ).trans
      (eqToIso (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm))

private noncomputable def unipotentPointIso (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, v, w} k H) :
    (FGComoduleCat.scalarExtensionFunctor k H K).obj M ≅
      (FGComoduleCat.scalarExtensionFunctor k H K).obj M :=
  (eqToIso (FGComoduleCat.scalarExtensionFunctor_obj k H K M)).trans
    (((GeneralLinearGroup.unipotentPart (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (Comodule.pointsAction M g))).toLinearEquiv.toModuleIsoₛ).trans
      (eqToIso (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm))

/-- The semisimple factors of the actions of a point on finite comodules form a natural
automorphism of scalar extension. -/
noncomputable def semisimplePointNatIso (g : WithConv (H →ₐ[k] K)) :
    FGComoduleCat.scalarExtensionFunctor k H K ≅
      FGComoduleCat.scalarExtensionFunctor k H K :=
  NatIso.ofComponents (semisimplePointIso k H K g) (fun {M N} f ↦ by
    rw [semisimplePointIso]
    -- Expose the private component constructor so naturality reduces to its underlying maps.
    change
      (FGComoduleCat.scalarExtensionFunctor k H K).map f ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K N) ≫
            (GeneralLinearGroup.semisimplePart
              (LinearMap.GeneralLinearGroup.ofLinearEquiv
                (Comodule.pointsAction N g))).toLinearEquiv.toModuleIsoₛ.hom ≫
              eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K N).symm =
        eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M) ≫
            (GeneralLinearGroup.semisimplePart
              (LinearMap.GeneralLinearGroup.ofLinearEquiv
                (Comodule.pointsAction M g))).toLinearEquiv.toModuleIsoₛ.hom ≫
              eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm ≫
                (FGComoduleCat.scalarExtensionFunctor k H K).map f
    rw [FGComoduleCat.scalarExtensionFunctor_map]
    simp only [Category.assoc]
    rw [cancel_epi]
    simp only [← Category.assoc]
    rw [cancel_mono]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      LinearEquiv.toModuleIsoₛ_hom]
    apply SemimoduleCat.hom_ext
    exact (GeneralLinearGroup.comp_semisimplePart_eq_of_comp_eq
      (f.hom.toLinearMap.baseChange K)
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g))
      (by
        have hM :
            (LinearMap.GeneralLinearGroup.ofLinearEquiv
              (Comodule.pointsAction M g) : Module.End K (K ⊗[k] M)) =
              Comodule.endOfPoint M g.ofConv :=
          Comodule.pointsAction_toLinearMap M g
        have hN :
            (LinearMap.GeneralLinearGroup.ofLinearEquiv
              (Comodule.pointsAction N g) : Module.End K (K ⊗[k] N)) =
              Comodule.endOfPoint N g.ofConv :=
          Comodule.pointsAction_toLinearMap N g
        rw [hM, hN]
        exact Comodule.baseChange_comp_endOfPoint f.hom g.ofConv)).symm)

/-- The unipotent factors of the actions of a point on finite comodules form a natural
automorphism of scalar extension. -/
noncomputable def unipotentPointNatIso (g : WithConv (H →ₐ[k] K)) :
    FGComoduleCat.scalarExtensionFunctor k H K ≅
      FGComoduleCat.scalarExtensionFunctor k H K :=
  NatIso.ofComponents (unipotentPointIso k H K g) (fun {M N} f ↦ by
    rw [unipotentPointIso]
    -- Expose the private component constructor so naturality reduces to its underlying maps.
    change
      (FGComoduleCat.scalarExtensionFunctor k H K).map f ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K N) ≫
            (GeneralLinearGroup.unipotentPart
              (LinearMap.GeneralLinearGroup.ofLinearEquiv
                (Comodule.pointsAction N g))).toLinearEquiv.toModuleIsoₛ.hom ≫
              eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K N).symm =
        eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M) ≫
            (GeneralLinearGroup.unipotentPart
              (LinearMap.GeneralLinearGroup.ofLinearEquiv
                (Comodule.pointsAction M g))).toLinearEquiv.toModuleIsoₛ.hom ≫
              eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm ≫
                (FGComoduleCat.scalarExtensionFunctor k H K).map f
    rw [FGComoduleCat.scalarExtensionFunctor_map]
    simp only [Category.assoc]
    rw [cancel_epi]
    simp only [← Category.assoc]
    rw [cancel_mono]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      LinearEquiv.toModuleIsoₛ_hom]
    apply SemimoduleCat.hom_ext
    exact (GeneralLinearGroup.comp_unipotentPart_eq_of_comp_eq
      (f.hom.toLinearMap.baseChange K)
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g))
      (by
        have hM :
            (LinearMap.GeneralLinearGroup.ofLinearEquiv
              (Comodule.pointsAction M g) : Module.End K (K ⊗[k] M)) =
              Comodule.endOfPoint M g.ofConv :=
          Comodule.pointsAction_toLinearMap M g
        have hN :
            (LinearMap.GeneralLinearGroup.ofLinearEquiv
              (Comodule.pointsAction N g) : Module.End K (K ⊗[k] N)) =
              Comodule.endOfPoint N g.ofConv :=
          Comodule.pointsAction_toLinearMap N g
        rw [hM, hN]
        exact Comodule.baseChange_comp_endOfPoint f.hom g.ofConv)).symm)

/-- The component of the semisimple-factor natural automorphism is the semisimple part of the
point action, transported across the scalar-extension functor's object equality. -/
@[simp]
theorem semisimplePointNatIso_hom_app (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, v, w} k H) :
    (semisimplePointNatIso k H K g).hom.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M) ≫
        (GeneralLinearGroup.semisimplePart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction M g))).toLinearEquiv.toModuleIsoₛ.hom ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm :=
  by
    rw [semisimplePointNatIso]
    -- `NatIso.ofComponents` computes to the private component at each object.
    change (semisimplePointIso k H K g M).hom = _
    rfl

/-- The component of the unipotent-factor natural automorphism is the unipotent part of the
point action, transported across the scalar-extension functor's object equality. -/
@[simp]
theorem unipotentPointNatIso_hom_app (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, v, w} k H) :
    (unipotentPointNatIso k H K g).hom.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M) ≫
        (GeneralLinearGroup.unipotentPart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction M g))).toLinearEquiv.toModuleIsoₛ.hom ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm :=
  by
    rw [unipotentPointNatIso]
    -- `NatIso.ofComponents` computes to the private component at each object.
    change (unipotentPointIso k H K g M).hom = _
    rfl

/-- The hom natural transformations of the semisimple and unipotent factors commute. -/
theorem semisimplePointNatIso_hom_comp_unipotentPointNatIso_hom
    (g : WithConv (H →ₐ[k] K)) :
    (semisimplePointNatIso k H K g).hom ≫ (unipotentPointNatIso k H K g).hom =
      (unipotentPointNatIso k H K g).hom ≫ (semisimplePointNatIso k H K g).hom := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, semisimplePointNatIso_hom_app,
    unipotentPointNatIso_hom_app, Category.assoc]
  rw [cancel_epi]
  simp only [← Category.assoc]
  rw [cancel_mono]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    LinearEquiv.toModuleIsoₛ_hom]
  apply SemimoduleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := congrArg
    ((↑·) : LinearMap.GeneralLinearGroup K (K ⊗[k] M) → Module.End K (K ⊗[k] M))
      (GeneralLinearGroup.commute_semisimplePart_unipotentPart
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))).eq.symm
  -- `toModuleIsoₛ` presents the factors through `toLinearEquiv`; the intertwining theorem
  -- presents the same maps through their underlying endomorphisms.
  change
    (GeneralLinearGroup.unipotentPart
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
        Module.End K (K ⊗[k] M))
      ((GeneralLinearGroup.semisimplePart
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
          Module.End K (K ⊗[k] M)) x) =
    (GeneralLinearGroup.semisimplePart
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
        Module.End K (K ⊗[k] M))
      ((GeneralLinearGroup.unipotentPart
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
          Module.End K (K ⊗[k] M)) x)
  exact LinearMap.congr_fun h x

/-- Composing the unipotent and semisimple hom natural transformations recovers the original
point action. This is the categorical order corresponding to multiplication of the underlying
linear automorphisms. -/
@[simp]
theorem unipotentPointNatIso_hom_comp_semisimplePointNatIso_hom
    (g : WithConv (H →ₐ[k] K)) :
    (unipotentPointNatIso k H K g).hom ≫ (semisimplePointNatIso k H K g).hom =
      (fgPointNatIsoHom k H K g).hom := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, semisimplePointNatIso_hom_app,
    unipotentPointNatIso_hom_app, fgPointNatIsoHom_hom_app, Category.assoc]
  rw [cancel_epi]
  simp only [← Category.assoc]
  rw [cancel_mono]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    LinearEquiv.toModuleIsoₛ_hom]
  apply SemimoduleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := congrArg
    ((↑·) : LinearMap.GeneralLinearGroup K (K ⊗[k] M) → Module.End K (K ⊗[k] M))
      (GeneralLinearGroup.semisimplePart_mul_unipotentPart
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)))
  -- As above, remove only the categorical and linear-equivalence wrappers around the same
  -- underlying endomorphisms.
  change
    (GeneralLinearGroup.semisimplePart
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
        Module.End K (K ⊗[k] M))
      ((GeneralLinearGroup.unipotentPart
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
          Module.End K (K ⊗[k] M)) x) =
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) :
      Module.End K (K ⊗[k] M)) x
  exact LinearMap.congr_fun h x

end TauCeti.Tannaka
