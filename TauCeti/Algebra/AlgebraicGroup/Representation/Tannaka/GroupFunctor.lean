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

Let `H` be a bialgebra over a commutative ring `R`. Sending a commutative `R`-algebra `A` to
the group of tensor automorphisms of scalar extension on the finite `H`-comodules is a functor

```text
CommAlgCat R ⥤ GrpCat,    A ↦ Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A),
```

with the action on morphisms given by base change of components
(`TauCeti.Tannaka.tensorAutMapValue`).

The functor needs no antipode: only the bialgebra structure enters. When `H` is moreover a Hopf
algebra over a field and is commutative, the pointwise Tannakian equivalence
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

-- `@[expose]` is required, not incidental: without the body, the coercion
-- `↑((tensorAutFunctor R H).obj A)` does not reduce to `Aut (...)`, so
-- `tensorAutFunctor_map_apply` below cannot even be stated, let alone proved.
/-- The tensor-automorphism group functor of a bialgebra: a commutative `R`-algebra `A` is
sent to the group of tensor automorphisms of scalar extension to `A` on the finite
`H`-comodules, and a morphism of value algebras acts by base change of components. -/
@[expose] noncomputable def tensorAutFunctor :
    CommAlgCat.{u} R ⥤ GrpCat.{max (u + 1) v} where
  obj A := GrpCat.of (Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
  map {A B} φ := GrpCat.ofHom (tensorAutMapValueHom R H A B φ.hom)
  map_id A := by
    refine GrpCat.hom_ext (MonoidHom.ext fun η ↦ ?_)
    simp only [GrpCat.hom_ofHom, tensorAutMapValueHom_apply, CommAlgCat.hom_id, GrpCat.hom_id,
      MonoidHom.id_apply]
    exact tensorAutMapValue_id R H A η
  map_comp {A B C} φ ψ := by
    refine GrpCat.hom_ext (MonoidHom.ext fun η ↦ ?_)
    simp only [GrpCat.hom_ofHom, tensorAutMapValueHom_apply, CommAlgCat.hom_comp,
      GrpCat.hom_comp, MonoidHom.coe_comp, Function.comp_apply]
    exact tensorAutMapValue_comp R H A B C φ.hom ψ.hom η

/-- The tensor-automorphism functor sends an algebra to its group of tensor automorphisms. -/
@[simp]
theorem tensorAutFunctor_obj (A : CommAlgCat.{u} R) :
    (tensorAutFunctor R H).obj A =
      GrpCat.of (Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :=
  rfl

/-- The tensor-automorphism functor acts on morphisms by base change of components. This is the
morphism-level form, stated with the object transports so that it stays in `simp` normal form
once `tensorAutFunctor_obj` fires; it matches
`TauCeti.GeneralLinear.scalarExtensionAutomorphismsFunctor_map`. -/
@[simp]
theorem tensorAutFunctor_map {A B : CommAlgCat.{u} R} (φ : A ⟶ B) :
    (tensorAutFunctor R H).map φ =
      eqToHom (tensorAutFunctor_obj R H A) ≫
        GrpCat.ofHom (tensorAutMapValueHom R H A B φ.hom) ≫
          eqToHom (tensorAutFunctor_obj R H B).symm := by
  apply (conj_eqToHom_iff_heq _ _ (tensorAutFunctor_obj R H A)
    (tensorAutFunctor_obj R H B)).2
  rfl

/-- The tensor-automorphism functor acts on morphisms by base change of components, in applied
form. Not a `simp` lemma: `tensorAutFunctor_obj` rewrites the object in the argument's type, so
this left-hand side is not in normal form; `tensorAutFunctor_map` carries the automation. -/
theorem tensorAutFunctor_map_apply {A B : CommAlgCat.{u} R} (φ : A ⟶ B)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :
    (tensorAutFunctor R H).map φ η = tensorAutMapValue R H A B φ.hom η := by
  -- The functor's action is the bundled base-change homomorphism; reducing the categorical
  -- and concrete-category wrappers exposes it, and its application lemma finishes.
  change tensorAutMapValueHom R H A B φ.hom η = _
  rw [tensorAutMapValueHom_apply]

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
      -- Both sides of the naturality square are, once evaluated, plain group-element
      -- equations. Reaching them by rewriting is not possible: the two composites are
      -- wrapped in the composite functor `pointsFunctor ⋙ uliftFunctor`, the universe lift's
      -- conjugation by `MulEquiv.ulift`, and `MulEquiv.toGrpIso`, none of which has a
      -- rewriting lemma for an application. All three reduce definitionally, so `change`
      -- states the evaluated square once, explicitly, and the two named lemmas finish.
      change fgPointTensorIsoEquiv k H B (AlgHom.mapValue φ.hom x.down) =
        (tensorAutFunctor k H).map φ (fgPointTensorIsoEquiv k H A x.down)
      rw [tensorAutFunctor_map_apply]
      exact fgPointTensorIsoEquiv_mapValue k H φ x.down)

/-- The natural Tannakian isomorphism sends a point to its tensor action. Not a `simp` lemma:
the argument's type is the composite functor's value, which `simp` rewrites, so the left-hand
side is not in normal form. -/
theorem pointsFunctorIsoTensorAutFunctor_hom_app_apply (A : CommAlgCat.{u} k)
    (x : ULift.{u + 1} (WithConv (H →ₐ[k] A))) :
    (pointsFunctorIsoTensorAutFunctor k H).hom.app A x = fgPointTensorIso k H A x.down := by
  -- As in the naturality proof above, the component is hidden behind `NatIso.ofComponents`
  -- and `MulEquiv.toGrpIso`; both reduce definitionally to the underlying multiplicative
  -- equivalence, which `change` names so its application lemmas apply. The closing `rfl`
  -- discharges `MulEquiv.ulift x = x.down`.
  change (MulEquiv.ulift.trans (fgPointTensorIsoEquiv k H A)) x = _
  rw [MulEquiv.trans_apply, fgPointTensorIsoEquiv_apply]
  rfl

/-- The inverse of the natural Tannakian isomorphism reconstructs the point of a tensor
automorphism. Not a `simp` lemma, for the same reason as the previous one. -/
theorem pointsFunctorIsoTensorAutFunctor_inv_app_apply (A : CommAlgCat.{u} k)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor k H A)) :
    ((pointsFunctorIsoTensorAutFunctor k H).inv.app A η).down =
      reconstructedPoint k H A η := by
  -- The inverse component is `(fgPointTensorIsoEquiv k H A).symm` conjugated by the universe
  -- lift; taking `.down` cancels the lift definitionally, so the statement is exactly the
  -- inverse-application lemma for the pointwise equivalence.
  have h : (fgPointTensorIsoEquiv k H A).symm η = reconstructedPoint k H A η :=
    fgPointTensorIsoEquiv_symm_apply k H A η
  exact h

end Reconstruction

end TauCeti.Tannaka
