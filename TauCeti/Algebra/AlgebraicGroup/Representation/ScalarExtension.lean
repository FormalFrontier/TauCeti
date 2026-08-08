/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic

/-!
# Scalar extension of finite comodules

Let `H` be a Hopf algebra over a commutative semiring `R`, and let `A` be a commutative
`R`-algebra. This file constructs the scalar extension of the underlying-module functor

```text
FGComoduleCat R H ⥤ SemimoduleCat A,    M ↦ A ⊗[R] M.
```

Every `A`-valued point of `H` acts naturally and invertibly on this functor: its component at
`M` is the usual point action on `A ⊗[R] M`.

This is the base change of the neutral underlying-module functor, without a faithfulness claim:
scalar extension along an arbitrary `R → A` need not be faithful. Equipping this functor and
these natural automorphisms with their tensor compatibilities is a separate step; together, the
constructions supply categorical infrastructure for Tannakian reconstruction in Layer 1 of the
reductive-groups roadmap.

## Main declarations

* `TauCeti.Tannaka.scalarExtensionFunctor`: scalar extension of the underlying-module functor on
  finite comodules.
* `TauCeti.Tannaka.pointIso`: the point action as an automorphism of one scalar extension.
* `TauCeti.Tannaka.pointNatIso`: the point action as a natural automorphism of the functor.

## References

This is the scalar-extended underlying-module functor and point action used in Tannakian
reconstruction; see
J. S. Milne, *Algebraic Groups* (2017), §§4.5 and 9.4. The construction reuses Mathlib's
linear-map base change and Tau Ceti's finite-comodule category and point action.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [HopfAlgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- Scalar extension of the underlying-module functor on finitely generated comodules. Over a
field, its source is the category of finite-dimensional representations, and it sends `M` to
`A ⊗[R] M`. No faithfulness property is asserted for the map `R → A`. -/
noncomputable abbrev scalarExtensionFunctor :
    FGComoduleCat.{u, v, u} R H ⥤ SemimoduleCat.{u} A :=
  { obj M := SemimoduleCat.of A (A ⊗[R] M)
    map f := SemimoduleCat.ofHom (f.hom.toLinearMap.baseChange A)
    map_id M := by
      apply SemimoduleCat.hom_ext
      exact TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ rfl
    map_comp f g := by
      apply SemimoduleCat.hom_ext
      exact TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ rfl }

/-- The carrier of the functor at `M` is the scalar extension `A ⊗[R] M`. -/
@[simp]
theorem scalarExtensionFunctor_obj_carrier (M : FGComoduleCat.{u, v, u} R H) :
    ((scalarExtensionFunctor R H A).obj M : Type u) = A ⊗[R] M :=
  rfl

/-- The linear map underlying the image of a comodule morphism is its scalar extension. -/
@[simp]
theorem scalarExtensionFunctor_map_hom {M N : FGComoduleCat.{u, v, u} R H} (f : M ⟶ N) :
    ((scalarExtensionFunctor R H A).map f).hom = f.hom.toLinearMap.baseChange A :=
  rfl

/-- An `A`-valued point of `H` acts by an automorphism on the scalar extension of each finite
comodule. -/
noncomputable def pointIso (g : WithConv (H →ₐ[R] A)) (M : FGComoduleCat.{u, v, u} R H) :
    (scalarExtensionFunctor R H A).obj M ≅ (scalarExtensionFunctor R H A).obj M :=
  let e := Comodule.pointsAction M.obj g
  { hom := ConcreteCategory.ofHom e.toLinearMap
    inv := ConcreteCategory.ofHom e.symm.toLinearMap
    hom_inv_id := by
      apply SemimoduleCat.hom_ext
      exact LinearMap.ext fun x ↦ e.symm_apply_apply x
    inv_hom_id := by
      apply SemimoduleCat.hom_ext
      exact LinearMap.ext fun x ↦ e.apply_symm_apply x }

/-- The linear map underlying the forward point automorphism is the usual point action. -/
@[simp]
theorem pointIso_hom_hom (g : WithConv (H →ₐ[R] A))
    (M : FGComoduleCat.{u, v, u} R H) :
    (pointIso R H A g M).hom.hom = Comodule.endOfPoint M.obj g.ofConv :=
  Comodule.pointsAction_toLinearMap M.obj g

/-- The linear map underlying the inverse point automorphism is the action of the inverse
convolution point. -/
@[simp]
theorem pointIso_inv_hom (g : WithConv (H →ₐ[R] A))
    (M : FGComoduleCat.{u, v, u} R H) :
    (pointIso R H A g M).inv.hom = Comodule.endOfPoint M.obj g⁻¹.ofConv := by
  rw [← Comodule.pointsAction_toLinearMap M.obj g⁻¹]
  exact congrArg LinearEquiv.toLinearMap (map_inv (Comodule.pointsAction M.obj) g).symm

/-- Every algebra-valued point acts as a natural automorphism of the scalar-extension functor.
Naturality is precisely the fact that scalar extension of a comodule morphism
intertwines point actions. -/
noncomputable def pointNatIso (g : WithConv (H →ₐ[R] A)) :
    scalarExtensionFunctor R H A ≅ scalarExtensionFunctor R H A :=
  NatIso.ofComponents (pointIso R H A g) (fun {M N} f ↦ by
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy]
    | tmul a m =>
        have h := LinearMap.congr_fun
          (Comodule.baseChange_comp_endOfPoint f.hom g.ofConv).symm (a ⊗ₜ[R] m)
        simp only [SemimoduleCat.hom_comp, pointIso_hom_hom, LinearMap.comp_apply]
        -- Remove the `SemimoduleCat` object projections so `h`, stated for the unbundled
        -- tensor-product modules, has exactly the displayed type.
        change Comodule.endOfPoint N.obj g.ofConv
            (f.hom.toLinearMap.baseChange A (a ⊗ₜ[R] m)) =
          f.hom.toLinearMap.baseChange A
            (Comodule.endOfPoint M.obj g.ofConv (a ⊗ₜ[R] m))
        exact h)

/-- The component of the point natural automorphism is the usual point action. -/
@[simp]
theorem pointNatIso_hom_app (g : WithConv (H →ₐ[R] A))
    (M : FGComoduleCat.{u, v, u} R H) :
    ((pointNatIso R H A g).hom.app M).hom =
      Comodule.endOfPoint M.obj g.ofConv :=
  pointIso_hom_hom R H A g M

/-- The inverse component of the point natural automorphism is the action of the inverse
convolution point. -/
@[simp]
theorem pointNatIso_inv_app (g : WithConv (H →ₐ[R] A))
    (M : FGComoduleCat.{u, v, u} R H) :
    ((pointNatIso R H A g).inv.app M).hom =
      Comodule.endOfPoint M.obj g⁻¹.ofConv :=
  pointIso_inv_hom R H A g M

end TauCeti.Tannaka
