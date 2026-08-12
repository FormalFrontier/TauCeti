/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ScalarExtension
public import TauCeti.LinearAlgebra.JordanChevalley.Functoriality

/-!
# Jordan factors of point actions

Let `H` be a Hopf algebra over a commutative semiring `k`, let `K` be a perfect extension field,
and let `g : H →ₐ[k] K` be a `K`-valued point. On every finite-dimensional `H`-comodule, `g`
acts by a linear automorphism after scalar extension to `K`. This file packages the semisimple
and unipotent parts of those automorphisms as natural automorphisms of the finite-comodule scalar
extension functor.

Naturality is substantive: a comodule morphism need be neither injective nor surjective. It follows
from functoriality of the multiplicative Jordan--Chevalley decomposition under arbitrary
intertwiners. The two natural factors commute and their product recovers the original point action
in the automorphism group of the scalar-extension functor.

Tensor compatibility is a separate downstream step. In the commutative coordinate-Hopf-algebra
setting of the roadmap, once the factors are tensor automorphisms, Tannakian reconstruction can
lift them from compatible actions on representations to points of the original affine group. This
is the representation-theoretic bridge in Layer 4 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.Tannaka.fgPointSemisimplePartNatIso`: the natural semisimple part of a point action.
* `TauCeti.Tannaka.fgPointUnipotentPartNatIso`: the natural unipotent part of a point action.
* `TauCeti.Tannaka.fgPointSemisimplePartNatIso_mul_fgPointUnipotentPartNatIso`: their product is
  the original point action.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v w x

variable (k : Type u) (H : Type v) (K : Type x) [CommSemiring k] [Semiring H]
  [HopfAlgebra k H] [Field K] [Algebra k K]

private theorem baseChange_comp_pointsAction {M N : FGComoduleCat.{u, v, w} k H}
    (f : M ⟶ N) (g : WithConv (H →ₐ[k] K)) :
    (f.hom.toLinearMap.baseChange K).comp
        (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) :
          Module.End K (K ⊗[k] M)) =
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g) :
          Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K) := by
  have hM :
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) :
        Module.End K (K ⊗[k] M)) = Comodule.endOfPoint M g.ofConv :=
    Comodule.pointsAction_toLinearMap M g
  have hN :
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g) :
        Module.End K (K ⊗[k] N)) = Comodule.endOfPoint N g.ofConv :=
    Comodule.pointsAction_toLinearMap N g
  rw [hM, hN]
  exact Comodule.baseChange_comp_endOfPoint f.hom g.ofConv

private theorem fgPointSemisimplePart_natural [PerfectField K]
    (g : WithConv (H →ₐ[k] K)) {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N) :
    (f.hom.toLinearMap.baseChange K).comp
        (GeneralLinearGroup.semisimplePart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
            Module.End K (K ⊗[k] M)) =
      (GeneralLinearGroup.semisimplePart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g)) :
            Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K) :=
  GeneralLinearGroup.comp_semisimplePart_eq_of_comp_eq
    (f.hom.toLinearMap.baseChange K)
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g))
    (baseChange_comp_pointsAction k H K f g)

private theorem fgPointUnipotentPart_natural [PerfectField K]
    (g : WithConv (H →ₐ[k] K)) {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N) :
    (f.hom.toLinearMap.baseChange K).comp
        (GeneralLinearGroup.unipotentPart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
            Module.End K (K ⊗[k] M)) =
      (GeneralLinearGroup.unipotentPart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g)) :
            Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K) :=
  GeneralLinearGroup.comp_unipotentPart_eq_of_comp_eq
    (f.hom.toLinearMap.baseChange K)
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g))
    (baseChange_comp_pointsAction k H K f g)

/-- The transported component isomorphism associated to a family of finite-comodule
automorphisms. -/
private noncomputable def fgPointFactorIso
    (φ : ∀ M : FGComoduleCat.{u, v, w} k H,
      LinearMap.GeneralLinearGroup K (K ⊗[k] M))
    (M : FGComoduleCat.{u, v, w} k H) :
    (FGComoduleCat.scalarExtensionFunctor k H K).obj M ≅
      (FGComoduleCat.scalarExtensionFunctor k H K).obj M :=
  (eqToIso (FGComoduleCat.scalarExtensionFunctor_obj k H K M)).trans
    ((φ M).toLinearEquiv.toModuleIsoₛ.trans
      (eqToIso (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm))

/-- A natural automorphism of finite-comodule scalar extension assembled from a pointwise family
of automorphisms and its intertwining property. -/
private noncomputable def fgPointFactorNatIso
    (φ : ∀ M : FGComoduleCat.{u, v, w} k H,
      LinearMap.GeneralLinearGroup K (K ⊗[k] M))
    (hφ : ∀ {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N),
      (f.hom.toLinearMap.baseChange K).comp (φ M : Module.End K (K ⊗[k] M)) =
        (φ N : Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K)) :
    Aut (FGComoduleCat.scalarExtensionFunctor k H K) :=
  NatIso.ofComponents (fgPointFactorIso k H K φ) (fun {M N} f ↦ by
    -- `NatIso.ofComponents` hides the private component constructor; reduce it once so its
    -- naturality can be proved through the public scalar-extension and linear-equivalence APIs.
    change
      (FGComoduleCat.scalarExtensionFunctor k H K).map f ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K N) ≫
            (φ N).toLinearEquiv.toModuleIsoₛ.hom ≫
              eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K N).symm =
        eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M) ≫
            (φ M).toLinearEquiv.toModuleIsoₛ.hom ≫
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
    exact (hφ f).symm)

@[simp]
private theorem fgPointFactorNatIso_hom_app
    (φ : ∀ M : FGComoduleCat.{u, v, w} k H,
      LinearMap.GeneralLinearGroup K (K ⊗[k] M))
    (hφ : ∀ {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N),
      (f.hom.toLinearMap.baseChange K).comp (φ M : Module.End K (K ⊗[k] M)) =
        (φ N : Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K))
    (M : FGComoduleCat.{u, v, w} k H) :
    (fgPointFactorNatIso k H K φ hφ).hom.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M) ≫
        (φ M).toLinearEquiv.toModuleIsoₛ.hom ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm :=
  rfl

@[simp]
private theorem fgPointFactorNatIso_inv_app
    (φ : ∀ M : FGComoduleCat.{u, v, w} k H,
      LinearMap.GeneralLinearGroup K (K ⊗[k] M))
    (hφ : ∀ {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N),
      (f.hom.toLinearMap.baseChange K).comp (φ M : Module.End K (K ⊗[k] M)) =
        (φ N : Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K))
    (M : FGComoduleCat.{u, v, w} k H) :
    (fgPointFactorNatIso k H K φ hφ).inv.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M) ≫
        (φ M).toLinearEquiv.toModuleIsoₛ.inv ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm :=
  rfl

private theorem fgPointFactor_mul_natural
    (φ ψ : ∀ M : FGComoduleCat.{u, v, w} k H,
      LinearMap.GeneralLinearGroup K (K ⊗[k] M))
    (hφ : ∀ {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N),
      (f.hom.toLinearMap.baseChange K).comp (φ M : Module.End K (K ⊗[k] M)) =
        (φ N : Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K))
    (hψ : ∀ {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N),
      (f.hom.toLinearMap.baseChange K).comp (ψ M : Module.End K (K ⊗[k] M)) =
        (ψ N : Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K))
    {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N) :
    (f.hom.toLinearMap.baseChange K).comp
        (φ M * ψ M : Module.End K (K ⊗[k] M)) =
      (φ N * ψ N : Module.End K (K ⊗[k] N)).comp
        (f.hom.toLinearMap.baseChange K) := by
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  have hφm := LinearMap.congr_fun (hφ f) ((ψ M : Module.End K (K ⊗[k] M)) m)
  have hψm := LinearMap.congr_fun (hψ f) m
  exact hφm.trans (congrArg (φ N : Module.End K (K ⊗[k] N)) hψm)

private theorem fgPointFactorNatIso_mul
    (φ ψ : ∀ M : FGComoduleCat.{u, v, w} k H,
      LinearMap.GeneralLinearGroup K (K ⊗[k] M))
    (hφ : ∀ {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N),
      (f.hom.toLinearMap.baseChange K).comp (φ M : Module.End K (K ⊗[k] M)) =
        (φ N : Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K))
    (hψ : ∀ {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N),
      (f.hom.toLinearMap.baseChange K).comp (ψ M : Module.End K (K ⊗[k] M)) =
        (ψ N : Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K)) :
    fgPointFactorNatIso k H K φ hφ * fgPointFactorNatIso k H K ψ hψ =
      fgPointFactorNatIso k H K (fun M ↦ φ M * ψ M)
        (fgPointFactor_mul_natural k H K φ ψ hφ hψ) := by
  apply Aut.ext
  apply NatTrans.ext
  funext M
  -- `Aut.ext` exposes the hom natural transformation but leaves group multiplication bundled;
  -- reduce its component to the reverse composition specified by `Aut.Aut_mul_def`.
  change
    (fgPointFactorNatIso k H K ψ hψ).hom.app M ≫
        (fgPointFactorNatIso k H K φ hφ).hom.app M = _
  simp only [fgPointFactorNatIso_hom_app, Category.assoc]
  rw [cancel_epi]
  simp only [← Category.assoc]
  rw [cancel_mono]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    LinearEquiv.toModuleIsoₛ_hom]
  apply SemimoduleCat.hom_ext
  simp only [SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom,
    LinearMap.GeneralLinearGroup.toLinearEquiv_mul, LinearEquiv.coe_toLinearMap_mul,
    Module.End.mul_eq_comp]

private theorem fgPointFactorNatIso_congr
    (φ ψ : ∀ M : FGComoduleCat.{u, v, w} k H,
      LinearMap.GeneralLinearGroup K (K ⊗[k] M))
    (hφ : ∀ {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N),
      (f.hom.toLinearMap.baseChange K).comp (φ M : Module.End K (K ⊗[k] M)) =
        (φ N : Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K))
    (hψ : ∀ {M N : FGComoduleCat.{u, v, w} k H} (f : M ⟶ N),
      (f.hom.toLinearMap.baseChange K).comp (ψ M : Module.End K (K ⊗[k] M)) =
        (ψ N : Module.End K (K ⊗[k] N)).comp (f.hom.toLinearMap.baseChange K))
    (h : ∀ M, φ M = ψ M) :
    fgPointFactorNatIso k H K φ hφ = fgPointFactorNatIso k H K ψ hψ := by
  apply Aut.ext
  apply NatTrans.ext
  funext M
  simp only [fgPointFactorNatIso_hom_app, h M]

variable [PerfectField K]

/-- The semisimple parts of a point's actions on finite comodules form an automorphism of scalar
extension. -/
noncomputable def fgPointSemisimplePartNatIso (g : WithConv (H →ₐ[k] K)) :
    Aut (FGComoduleCat.scalarExtensionFunctor k H K) :=
  fgPointFactorNatIso k H K
    (fun M ↦ GeneralLinearGroup.semisimplePart
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)))
    (fgPointSemisimplePart_natural k H K g)

/-- The unipotent parts of a point's actions on finite comodules form an automorphism of scalar
extension. -/
noncomputable def fgPointUnipotentPartNatIso (g : WithConv (H →ₐ[k] K)) :
    Aut (FGComoduleCat.scalarExtensionFunctor k H K) :=
  fgPointFactorNatIso k H K
    (fun M ↦ GeneralLinearGroup.unipotentPart
      (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)))
    (fgPointUnipotentPart_natural k H K g)

/-- The hom component of the semisimple-part automorphism is the semisimple part of the point
action, transported across the scalar-extension functor's object equality. -/
@[simp]
theorem fgPointSemisimplePartNatIso_hom_app (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, v, w} k H) :
    (fgPointSemisimplePartNatIso k H K g).hom.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M) ≫
        (GeneralLinearGroup.semisimplePart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction M g))).toLinearEquiv.toModuleIsoₛ.hom ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm :=
  fgPointFactorNatIso_hom_app k H K _ (fgPointSemisimplePart_natural k H K g) M

/-- The inverse component of the semisimple-part automorphism is the inverse semisimple part of
the point action, transported across the scalar-extension functor's object equality. -/
@[simp]
theorem fgPointSemisimplePartNatIso_inv_app (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, v, w} k H) :
    (fgPointSemisimplePartNatIso k H K g).inv.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M) ≫
        (GeneralLinearGroup.semisimplePart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction M g))).toLinearEquiv.toModuleIsoₛ.inv ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm :=
  fgPointFactorNatIso_inv_app k H K _ (fgPointSemisimplePart_natural k H K g) M

/-- The hom component of the unipotent-part automorphism is the unipotent part of the point action,
transported across the scalar-extension functor's object equality. -/
@[simp]
theorem fgPointUnipotentPartNatIso_hom_app (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, v, w} k H) :
    (fgPointUnipotentPartNatIso k H K g).hom.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M) ≫
        (GeneralLinearGroup.unipotentPart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction M g))).toLinearEquiv.toModuleIsoₛ.hom ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm :=
  fgPointFactorNatIso_hom_app k H K _ (fgPointUnipotentPart_natural k H K g) M

/-- The inverse component of the unipotent-part automorphism is the inverse unipotent part of the
point action, transported across the scalar-extension functor's object equality. -/
@[simp]
theorem fgPointUnipotentPartNatIso_inv_app (g : WithConv (H →ₐ[k] K))
    (M : FGComoduleCat.{u, v, w} k H) :
    (fgPointUnipotentPartNatIso k H K g).inv.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M) ≫
        (GeneralLinearGroup.unipotentPart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction M g))).toLinearEquiv.toModuleIsoₛ.inv ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj k H K M).symm :=
  fgPointFactorNatIso_inv_app k H K _ (fgPointUnipotentPart_natural k H K g) M

/-- The semisimple- and unipotent-part automorphisms of a point action commute. -/
theorem commute_fgPointSemisimplePartNatIso_fgPointUnipotentPartNatIso
    (g : WithConv (H →ₐ[k] K)) :
    Commute (fgPointSemisimplePartNatIso k H K g)
      (fgPointUnipotentPartNatIso k H K g) := by
  rw [commute_iff_eq]
  rw [fgPointSemisimplePartNatIso, fgPointUnipotentPartNatIso,
    fgPointFactorNatIso_mul, fgPointFactorNatIso_mul]
  apply fgPointFactorNatIso_congr
  intro M
  exact (GeneralLinearGroup.commute_semisimplePart_unipotentPart
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))).eq

/-- Multiplying the semisimple- and unipotent-part automorphisms recovers the original point
action. -/
@[simp]
theorem fgPointSemisimplePartNatIso_mul_fgPointUnipotentPartNatIso
    (g : WithConv (H →ₐ[k] K)) :
    fgPointSemisimplePartNatIso k H K g * fgPointUnipotentPartNatIso k H K g =
      fgPointNatIsoHom k H K g := by
  rw [fgPointSemisimplePartNatIso, fgPointUnipotentPartNatIso,
    fgPointFactorNatIso_mul]
  apply Aut.ext
  apply NatTrans.ext
  funext M
  simp only [fgPointFactorNatIso_hom_app, fgPointNatIsoHom_hom_app]
  rw [GeneralLinearGroup.semisimplePart_mul_unipotentPart]
  have haction :
      (LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Comodule.pointsAction M g)).toLinearEquiv = Comodule.pointsAction M g :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (K ⊗[k] M)).apply_symm_apply
      (Comodule.pointsAction M g)
  rw [haction]

end TauCeti.Tannaka
