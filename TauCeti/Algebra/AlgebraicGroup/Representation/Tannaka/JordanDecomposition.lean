/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ScalarExtension
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Monoidal
public import TauCeti.LinearAlgebra.JordanChevalley.Functoriality
public import TauCeti.LinearAlgebra.JordanChevalley.TensorProduct

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

The final section combines this naturality with tensor-product compatibility of multiplicative
Jordan decomposition. Thus both factors are tensor automorphisms. In the commutative
coordinate-Hopf-algebra setting of the roadmap, Tannakian reconstruction can now lift them from
compatible actions on representations to points of the original affine group. This is the
representation-theoretic bridge in Layer 4 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.Tannaka.fgPointSemisimplePartNatIso`: the natural semisimple part of a point action.
* `TauCeti.Tannaka.fgPointUnipotentPartNatIso`: the natural unipotent part of a point action.
* `TauCeti.Tannaka.fgPointSemisimplePartTensorIso`: the semisimple factors as a tensor
  automorphism.
* `TauCeti.Tannaka.fgPointUnipotentPartTensorIso`: the unipotent factors as a tensor
  automorphism.
* `TauCeti.Tannaka.fgPointSemisimplePartNatIso_mul_fgPointUnipotentPartNatIso`: their product is
  the original point action.
* `TauCeti.Tannaka.fgPointSemisimplePartTensorIso_mul_fgPointUnipotentPartTensorIso`: the same
  factorization among tensor automorphisms.

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

section Monoidal

open MonoidalCategory

variable (k : Type u) (H : Type v) (K : Type u) [Field k] [Semiring H]
  [HopfAlgebra k H] [Field K] [Algebra k K] [PerfectField K]

omit [PerfectField K] in
private theorem ofLinearEquiv_pointsAction_tensorUnit_eq_one
    (g : WithConv (H →ₐ[k] K)) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv
        (Comodule.pointsAction (𝟙_ (FGComoduleCat k H)) g) = 1 := by
  apply Units.ext
  -- Equality in the general linear group reduces to the underlying point endomorphism, where
  -- the trivial-comodule action theorem applies directly.
  change (Comodule.pointsAction (𝟙_ (FGComoduleCat k H)) g :
    K ⊗[k] (𝟙_ (FGComoduleCat k H)) →ₗ[K] K ⊗[k] (𝟙_ (FGComoduleCat k H))) =
      LinearMap.id
  rw [Comodule.pointsAction_toLinearMap, Comodule.endOfPoint_trivial]

omit [PerfectField K] in
private theorem coe_ofLinearEquiv_pointsAction
    (g : WithConv (H →ₐ[k] K)) (M : FGComoduleCat.{u, v, u} k H) :
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g) :
      Module.End K (K ⊗[k] M)) = Comodule.endOfPoint M g.ofConv :=
  Comodule.pointsAction_toLinearMap M g

omit [PerfectField K] in
private theorem distribBaseChange_comp_pointsAction
    (g : WithConv (H →ₐ[k] K)) (M N : FGComoduleCat.{u, v, u} k H) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap.comp
        (GeneralLinearGroup.tensorProduct
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
          (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g)) :
          Module.End K ((K ⊗[k] M) ⊗[K] (K ⊗[k] N))) =
      (LinearMap.GeneralLinearGroup.ofLinearEquiv
          (Comodule.pointsAction (M ⊗ N : FGComoduleCat k H) g) :
        Module.End K (K ⊗[k] ((M ⊗ N : FGComoduleCat k H) : Type u))).comp
          (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap := by
  let _ : Comodule k H (M ⊗[k] N) :=
    inferInstanceAs (Comodule k H ((M ⊗ N : FGComoduleCat k H) : Type u))
  let d := (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap
  let a := GeneralLinearGroup.tensorProduct
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g))
  let b := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (Comodule.pointsAction (M ⊗ N : FGComoduleCat k H) g)
  let dc :
      (SemimoduleCat.of K (K ⊗[k] M) ⊗ SemimoduleCat.of K (K ⊗[k] N)) ⟶
        SemimoduleCat.of K (K ⊗[k] (M ⊗[k] N)) :=
    SemimoduleCat.ofHom d
  have htensor :
        (SemimoduleCat.ofHom (Comodule.endOfPoint M g.ofConv) ⊗ₘ
            SemimoduleCat.ofHom (Comodule.endOfPoint N g.ofConv)) ≫ dc =
      dc ≫ SemimoduleCat.ofHom (Comodule.endOfPoint
        ((M ⊗ N : FGComoduleCat k H) : Type u) g.ofConv) := by
    apply SemimoduleCat.hom_ext
    exact Comodule.endOfPoint_tensor_of_coact_eq (R := k) (H := H) (A := K)
      (V := M) (W := N) (FGComoduleCat.tensor_coact (R := k) (C := H) M N) g.ofConv
  have hlin := congrArg SemimoduleCat.Hom.hom htensor
  simp only [SemimoduleCat.hom_comp] at hlin
  rw [SemimoduleCat.hom_tensorHom] at hlin
  -- The categorical tensor source and the explicit tensor-product module are definitionally
  -- identified only inside `SemimoduleCat`; display the resulting linear maps after forgetting.
  change d.comp (TensorProduct.map (Comodule.endOfPoint M g.ofConv)
      (Comodule.endOfPoint N g.ofConv)) =
    (Comodule.endOfPoint ((M ⊗ N : FGComoduleCat k H) : Type u) g.ofConv).comp d at hlin
  simpa only [d, a, b, GeneralLinearGroup.coe_tensorProduct,
    coe_ofLinearEquiv_pointsAction] using hlin

private theorem distribBaseChange_comp_semisimplePart_pointsAction
    (g : WithConv (H →ₐ[k] K)) (M N : FGComoduleCat.{u, v, u} k H) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap.comp
        (GeneralLinearGroup.tensorProduct
          (GeneralLinearGroup.semisimplePart
            (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)))
          (GeneralLinearGroup.semisimplePart
            (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g))) :
          Module.End K ((K ⊗[k] M) ⊗[K] (K ⊗[k] N))) =
      (GeneralLinearGroup.semisimplePart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction (M ⊗ N : FGComoduleCat k H) g)) :
        Module.End K (K ⊗[k] ((M ⊗ N : FGComoduleCat k H) : Type u))).comp
          (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap := by
  let d := (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap
  let a := GeneralLinearGroup.tensorProduct
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g))
  let b := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (Comodule.pointsAction (M ⊗ N : FGComoduleCat k H) g)
  have hab : d.comp (a : Module.End K ((K ⊗[k] M) ⊗[K] (K ⊗[k] N))) =
      (b : Module.End K (K ⊗[k] ((M ⊗ N : FGComoduleCat k H) : Type u))).comp d :=
    distribBaseChange_comp_pointsAction k H K g M N
  have h := GeneralLinearGroup.comp_semisimplePart_eq_of_comp_eq
    (K := K) (V := (K ⊗[k] M) ⊗[K] (K ⊗[k] N))
      (W := K ⊗[k] ((M ⊗ N : FGComoduleCat k H) : Type u)) d a b hab
  simpa only [d, a, b, GeneralLinearGroup.semisimplePart_tensorProduct] using h

private theorem distribBaseChange_comp_unipotentPart_pointsAction
    (g : WithConv (H →ₐ[k] K)) (M N : FGComoduleCat.{u, v, u} k H) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap.comp
        (GeneralLinearGroup.tensorProduct
          (GeneralLinearGroup.unipotentPart
            (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)))
          (GeneralLinearGroup.unipotentPart
            (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g))) :
          Module.End K ((K ⊗[k] M) ⊗[K] (K ⊗[k] N))) =
      (GeneralLinearGroup.unipotentPart
          (LinearMap.GeneralLinearGroup.ofLinearEquiv
            (Comodule.pointsAction (M ⊗ N : FGComoduleCat k H) g)) :
        Module.End K (K ⊗[k] ((M ⊗ N : FGComoduleCat k H) : Type u))).comp
          (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap := by
  let d := (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap
  let a := GeneralLinearGroup.tensorProduct
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g))
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g))
  let b := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (Comodule.pointsAction (M ⊗ N : FGComoduleCat k H) g)
  have hab : d.comp (a : Module.End K ((K ⊗[k] M) ⊗[K] (K ⊗[k] N))) =
      (b : Module.End K (K ⊗[k] ((M ⊗ N : FGComoduleCat k H) : Type u))).comp d :=
    distribBaseChange_comp_pointsAction k H K g M N
  have h := GeneralLinearGroup.comp_unipotentPart_eq_of_comp_eq
    (K := K) (V := (K ⊗[k] M) ⊗[K] (K ⊗[k] N))
      (W := K ⊗[k] ((M ⊗ N : FGComoduleCat k H) : Type u)) d a b hab
  simpa only [d, a, b, GeneralLinearGroup.unipotentPart_tensorProduct] using h

private theorem isMonoidal_fgPointSemisimplePartNatIso_hom
    (g : WithConv (H →ₐ[k] K)) :
    NatTrans.IsMonoidal (fgPointSemisimplePartNatIso k H K g).hom := by
  constructor
  · rw [FGComoduleCat.scalarExtensionFunctor_ε,
      fgPointSemisimplePartNatIso_hom_app]
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro a
    simp only [Category.assoc, SemimoduleCat.comp_apply,
      LinearEquiv.toModuleIsoₛ_hom]
    rw [ofLinearEquiv_pointsAction_tensorUnit_eq_one k H K g,
      GeneralLinearGroup.semisimplePart_eq_self GeneralLinearGroup.isSemisimple_one]
    simp
  · intro M N
    have htensor :
        SemimoduleCat.ofHom
              (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap ≫
            SemimoduleCat.ofHom
              (GeneralLinearGroup.semisimplePart
                (LinearMap.GeneralLinearGroup.ofLinearEquiv
                  (Comodule.pointsAction (M ⊗ N : FGComoduleCat k H) g)) :
                Module.End K (K ⊗[k] ((M ⊗ N : FGComoduleCat k H) : Type u))) =
          (SemimoduleCat.ofHom
                (GeneralLinearGroup.semisimplePart
                  (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
                  Module.End K (K ⊗[k] M)) ⊗ₘ
              SemimoduleCat.ofHom
                (GeneralLinearGroup.semisimplePart
                  (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g)) :
                  Module.End K (K ⊗[k] N))) ≫
            SemimoduleCat.ofHom
              (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap := by
      apply SemimoduleCat.hom_ext
      -- Forget the categorical tensor product so the transported intertwining identity is stated
      -- directly with `TensorProduct.map` on the explicit scalar extensions.
      change
        (GeneralLinearGroup.semisimplePart
            (LinearMap.GeneralLinearGroup.ofLinearEquiv
              (Comodule.pointsAction (M ⊗ N : FGComoduleCat k H) g)) :
          Module.End K (K ⊗[k] ((M ⊗ N : FGComoduleCat k H) : Type u))).comp
            (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap =
          (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap.comp
            (TensorProduct.map
              (GeneralLinearGroup.semisimplePart
                (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
                Module.End K (K ⊗[k] M))
              (GeneralLinearGroup.semisimplePart
                (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g)) :
                Module.End K (K ⊗[k] N)))
      simpa only [GeneralLinearGroup.coe_tensorProduct] using
        (distribBaseChange_comp_semisimplePart_pointsAction k H K g M N).symm
    erw [FGComoduleCat.scalarExtensionFunctor_μ,
      fgPointSemisimplePartNatIso_hom_app,
      fgPointSemisimplePartNatIso_hom_app,
      fgPointSemisimplePartNatIso_hom_app]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [cancel_epi]
    erw [Category.assoc, eqToHom_trans_assoc]
    simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc, eqToHom_trans,
      eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.toModuleIsoₛ_hom]
    erw [← Category.assoc, htensor, Category.assoc]

private theorem isMonoidal_fgPointUnipotentPartNatIso_hom
    (g : WithConv (H →ₐ[k] K)) :
    NatTrans.IsMonoidal (fgPointUnipotentPartNatIso k H K g).hom := by
  constructor
  · rw [FGComoduleCat.scalarExtensionFunctor_ε,
      fgPointUnipotentPartNatIso_hom_app]
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro a
    simp only [Category.assoc, SemimoduleCat.comp_apply,
      LinearEquiv.toModuleIsoₛ_hom]
    rw [ofLinearEquiv_pointsAction_tensorUnit_eq_one k H K g,
      GeneralLinearGroup.unipotentPart_eq_self GeneralLinearGroup.isUnipotent_one]
    simp
  · intro M N
    have htensor :
        SemimoduleCat.ofHom
              (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap ≫
            SemimoduleCat.ofHom
              (GeneralLinearGroup.unipotentPart
                (LinearMap.GeneralLinearGroup.ofLinearEquiv
                  (Comodule.pointsAction (M ⊗ N : FGComoduleCat k H) g)) :
                Module.End K (K ⊗[k] ((M ⊗ N : FGComoduleCat k H) : Type u))) =
          (SemimoduleCat.ofHom
                (GeneralLinearGroup.unipotentPart
                  (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
                  Module.End K (K ⊗[k] M)) ⊗ₘ
              SemimoduleCat.ofHom
                (GeneralLinearGroup.unipotentPart
                  (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g)) :
                  Module.End K (K ⊗[k] N))) ≫
            SemimoduleCat.ofHom
              (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap := by
      apply SemimoduleCat.hom_ext
      -- As in the semisimple case, expose the linear maps beneath the categorical tensor square.
      change
        (GeneralLinearGroup.unipotentPart
            (LinearMap.GeneralLinearGroup.ofLinearEquiv
              (Comodule.pointsAction (M ⊗ N : FGComoduleCat k H) g)) :
          Module.End K (K ⊗[k] ((M ⊗ N : FGComoduleCat k H) : Type u))).comp
            (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap =
          (TensorProduct.AlgebraTensorModule.distribBaseChange k K M N).symm.toLinearMap.comp
            (TensorProduct.map
              (GeneralLinearGroup.unipotentPart
                (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)) :
                Module.End K (K ⊗[k] M))
              (GeneralLinearGroup.unipotentPart
                (LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction N g)) :
                Module.End K (K ⊗[k] N)))
      simpa only [GeneralLinearGroup.coe_tensorProduct] using
        (distribBaseChange_comp_unipotentPart_pointsAction k H K g M N).symm
    erw [FGComoduleCat.scalarExtensionFunctor_μ,
      fgPointUnipotentPartNatIso_hom_app,
      fgPointUnipotentPartNatIso_hom_app,
      fgPointUnipotentPartNatIso_hom_app]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [cancel_epi]
    erw [Category.assoc, eqToHom_trans_assoc]
    simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc, eqToHom_trans,
      eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.toModuleIsoₛ_hom]
    erw [← Category.assoc, htensor, Category.assoc]

/-- The semisimple factors of a point's actions on finite comodules, as an automorphism of the
monoidal scalar-extension functor. -/
noncomputable def fgPointSemisimplePartTensorIso (g : WithConv (H →ₐ[k] K)) :
    Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H K) :=
  @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _
    (fgPointSemisimplePartNatIso k H K g)
    (isMonoidal_fgPointSemisimplePartNatIso_hom k H K g)

/-- The unipotent factors of a point's actions on finite comodules, as an automorphism of the
monoidal scalar-extension functor. -/
noncomputable def fgPointUnipotentPartTensorIso (g : WithConv (H →ₐ[k] K)) :
    Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H K) :=
  @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _
    (fgPointUnipotentPartNatIso k H K g)
    (isMonoidal_fgPointUnipotentPartNatIso_hom k H K g)

/-- Forgetting tensor compatibility from the semisimple-factor automorphism recovers its
underlying natural automorphism. -/
@[simp]
theorem fgPointSemisimplePartTensorIso_hom_hom (g : WithConv (H →ₐ[k] K)) :
    (fgPointSemisimplePartTensorIso k H K g).hom.hom =
      (fgPointSemisimplePartNatIso k H K g).hom :=
  (rfl)

/-- Forgetting tensor compatibility from the unipotent-factor automorphism recovers its
underlying natural automorphism. -/
@[simp]
theorem fgPointUnipotentPartTensorIso_hom_hom (g : WithConv (H →ₐ[k] K)) :
    (fgPointUnipotentPartTensorIso k H K g).hom.hom =
      (fgPointUnipotentPartNatIso k H K g).hom :=
  (rfl)

/-- The tensor automorphisms formed by the semisimple and unipotent factors commute. -/
theorem commute_fgPointSemisimplePartTensorIso_fgPointUnipotentPartTensorIso
    (g : WithConv (H →ₐ[k] K)) :
    Commute (fgPointSemisimplePartTensorIso k H K g)
      (fgPointUnipotentPartTensorIso k H K g) := by
  rw [commute_iff_eq]
  apply Aut.ext
  apply LaxMonoidalFunctor.hom_ext
  exact congrArg Iso.hom
    (commute_fgPointSemisimplePartNatIso_fgPointUnipotentPartNatIso k H K g).eq

/-- Multiplying the tensor automorphisms formed by the semisimple and unipotent factors recovers
the tensor automorphism induced by the original point. -/
@[simp]
theorem fgPointSemisimplePartTensorIso_mul_fgPointUnipotentPartTensorIso
    (g : WithConv (H →ₐ[k] K)) :
    fgPointSemisimplePartTensorIso k H K g * fgPointUnipotentPartTensorIso k H K g =
      fgPointTensorIso k H K g := by
  apply Aut.ext
  apply LaxMonoidalFunctor.hom_ext
  rw [fgPointTensorIso_hom_hom]
  exact congrArg Iso.hom
    (fgPointSemisimplePartNatIso_mul_fgPointUnipotentPartNatIso k H K g)

end Monoidal

end TauCeti.Tannaka
