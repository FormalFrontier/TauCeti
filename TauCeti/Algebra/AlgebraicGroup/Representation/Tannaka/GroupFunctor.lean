/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.PointsFunctor
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Equivalence

/-!
# The tensor-automorphism group functor and natural Tannakian reconstruction

Let `H` be a Hopf algebra over a commutative ring `R`. Sending a commutative `R`-algebra `A` to
the group of tensor automorphisms of scalar extension on the finite `H`-comodules is a functor

```text
CommAlgCat R ⥤ GrpCat,    A ↦ Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A),
```

with the action on morphisms given by base change of components
(`TauCeti.Tannaka.tensorAutMapValue`).

When `R` is a field and `H` is commutative, the pointwise Tannakian equivalence
`TauCeti.Tannaka.fgPointTensorIsoEquiv` is natural in `A`, so the functor of points of `H` is
isomorphic to this tensor-automorphism functor. This is the group-functor form of Tannakian
reconstruction: it identifies the two as functors of points, not merely group by group.

Tensor automorphisms of scalar extension live one universe above the comodules, while the points
of `H` live in the universe of the value algebra, so the comparison is stated after the standard
universe lift of the points functor.

## Main declarations

* `TauCeti.Tannaka.tensorAutFunctor`: the tensor-automorphism group functor on commutative
  algebras.
* `TauCeti.Tannaka.pointsFunctorIsoTensorAutFunctor`: the Tannakian equivalence as a natural
  isomorphism of group-valued functors.

## References

* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory

namespace TauCeti.Tannaka

universe u v

section Functor

variable (R : Type u) [CommRing R]
variable (H : Type v) [Semiring H] [Bialgebra R H]

/-- The tensor-automorphism group functor of a Hopf algebra: a commutative `R`-algebra `A` is
sent to the group of tensor automorphisms of scalar extension to `A` on the finite
`H`-comodules, and a morphism of value algebras acts by base change of components. -/
@[expose] noncomputable def tensorAutFunctor :
    CommAlgCat.{u} R ⥤ GrpCat.{max (u + 1) v} where
  obj A := GrpCat.of (Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
  map {A B} φ := GrpCat.ofHom (tensorAutMapValueHom R H A B φ.hom)
  map_id A := by
    refine GrpCat.hom_ext (MonoidHom.ext fun η ↦ ?_)
    exact tensorAutMapValue_id R H A η
  map_comp {A B C} φ ψ := by
    refine GrpCat.hom_ext (MonoidHom.ext fun η ↦ ?_)
    exact tensorAutMapValue_comp R H A B C φ.hom ψ.hom η

/-- The tensor-automorphism functor sends an algebra to its group of tensor automorphisms. -/
theorem tensorAutFunctor_obj (A : CommAlgCat.{u} R) :
    (tensorAutFunctor R H).obj A =
      GrpCat.of (Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :=
  rfl

/-- The tensor-automorphism functor acts on morphisms by base change of components. -/
@[simp]
theorem tensorAutFunctor_map_apply {A B : CommAlgCat.{u} R} (φ : A ⟶ B)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :
    (tensorAutFunctor R H).map φ η = tensorAutMapValue R H A B φ.hom η :=
  rfl

end Functor

section Reconstruction

variable (k H : Type u) [Field k] [CommRing H] [HopfAlgebra k H]

/-- The pointwise Tannakian equivalence commutes with base change of the value algebra. -/
private theorem fgPointTensorIsoEquiv_mapValue {A B : CommAlgCat.{u} k} (φ : A ⟶ B)
    (g : WithConv (H →ₐ[k] A)) :
    fgPointTensorIsoEquiv k H B (AlgHom.mapValue φ.hom g) =
      tensorAutMapValue k H A B φ.hom (fgPointTensorIsoEquiv k H A g) := by
  rw [fgPointTensorIsoEquiv_apply, fgPointTensorIsoEquiv_apply,
    tensorAutMapValue_fgPointTensorIso]

/-- Tannakian reconstruction as a natural isomorphism of group-valued functors on commutative
`k`-algebras: the functor of points of `H` is isomorphic to its tensor-automorphism functor.

The points functor is composed with the universe lift because tensor automorphisms of
scalar extension live one universe above the value algebra. -/
noncomputable def pointsFunctorIsoTensorAutFunctor :
    HopfAlgebra.pointsFunctor (R := k) (H := H) ⋙ GrpCat.uliftFunctor.{u + 1, u} ≅
      tensorAutFunctor k H :=
  NatIso.ofComponents
    (fun A ↦ (MulEquiv.ulift.trans (fgPointTensorIsoEquiv k H A)).toGrpIso)
    (fun {A B} φ ↦ by
      refine GrpCat.hom_ext (MonoidHom.ext fun x ↦ ?_)
      change fgPointTensorIsoEquiv k H B (AlgHom.mapValue φ.hom x.down) =
        tensorAutMapValue k H A B φ.hom (fgPointTensorIsoEquiv k H A x.down)
      exact fgPointTensorIsoEquiv_mapValue k H φ x.down)

/-- The natural Tannakian isomorphism sends a point to its tensor action. Not a `simp` lemma:
the argument's type is the composite functor's value, which `simp` rewrites, so the left-hand
side is not in normal form. -/
theorem pointsFunctorIsoTensorAutFunctor_hom_app_apply (A : CommAlgCat.{u} k)
    (x : ULift.{u + 1} (WithConv (H →ₐ[k] A))) :
    (pointsFunctorIsoTensorAutFunctor k H).hom.app A x = fgPointTensorIso k H A x.down := by
  change (MulEquiv.ulift.trans (fgPointTensorIsoEquiv k H A)) x = _
  rw [MulEquiv.trans_apply, fgPointTensorIsoEquiv_apply]
  rfl

/-- The inverse of the natural Tannakian isomorphism reconstructs the point of a tensor
automorphism. Not a `simp` lemma, for the same reason as the previous one. -/
theorem pointsFunctorIsoTensorAutFunctor_inv_app_apply (A : CommAlgCat.{u} k)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) :
    ((pointsFunctorIsoTensorAutFunctor k H).inv.app A η).down =
      reconstructedPoint k H A η := by
  have h : (fgPointTensorIsoEquiv k H A).symm η = reconstructedPoint k H A η :=
    fgPointTensorIsoEquiv_symm_apply k H A η
  exact h

end Reconstruction

end TauCeti.Tannaka
