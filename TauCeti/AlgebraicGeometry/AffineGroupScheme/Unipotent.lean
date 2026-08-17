/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.FiniteType
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth

/-!
# Smooth unipotent affine group schemes

This file transports smooth unipotence from finite-type commutative Hopf algebras to affine
group schemes of finite type over a field. The coordinate-ring predicate says that the algebra is
smooth and that every point over an algebraic closure acts unipotently in every finite-dimensional
comodule. Smoothness is explicit: geometric points alone do not detect the infinitesimal structure
of a nonreduced group scheme.

The resulting full subcategory is anti-equivalent to smooth unipotent commutative Hopf algebras.
This synchronizes the coordinate-ring and scheme models of unipotent groups and supplies the
scheme-side predicate needed to formulate reductivity using normal closed subgroup schemes.

## Main declarations

* `TauCeti.smoothUnipotentAffineGroupSchemeProperty`: smooth unipotence for finite-type affine
  group schemes over a field.
* `TauCeti.smoothUnipotentAffineGroupSchemeProperty_iff`: its coordinate-ring characterization.
* `TauCeti.SmoothUnipotentAffineGroupSchemeCat`: the corresponding full subcategory.
* `TauCeti.smoothUnipotentCommHopfAlgCatOpEquivSmoothUnipotentAffineGroupSchemeCat`: the
  restricted affine Hopf/group-scheme anti-equivalence.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This advances Layer 5, "Unipotent groups", of the ReductiveGroups roadmap. It is the scheme-side
form of the smooth geometric definition and a direct prerequisite for Layer 6, where reductivity
is defined by excluding nontrivial connected normal unipotent closed subgroup schemes after
geometric base change.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite WithConv

universe u

/-- The object property selecting smooth unipotent affine group schemes of finite type over a
field.

The property is transported through the finite-type affine Hopf/group-scheme anti-equivalence.
Thus it retains the representation-theoretic coordinate-ring criterion while presenting it on
the scheme side, without making smoothness implicit in the ambient category. -/
def smoothUnipotentAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :=
  (smoothUnipotentCommHopfAlgProperty k).op.inverseImage
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse

/-- A finite-type affine group scheme is smooth unipotent exactly when the coordinate Hopf
algebra supplied by the affine anti-equivalence is smooth and every geometric point acts
unipotently in every finite-dimensional comodule. -/
@[simp]
theorem smoothUnipotentAffineGroupSchemeProperty_iff
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :
    smoothUnipotentAffineGroupSchemeProperty k G ↔
      Algebra.Smooth k
          ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj G).unop ∧
        ∀ g : WithConv
            (((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj G).unop
              →ₐ[k] AlgebraicClosure k),
          HopfAlgebra.IsUnipotentPoint g :=
  smoothUnipotentCommHopfAlgProperty_iff k
    ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj G).unop

/-- Smooth unipotence of finite-type affine group schemes is invariant under isomorphism. -/
instance (k : Type u) [Field k] :
    (smoothUnipotentAffineGroupSchemeProperty k).IsClosedUnderIsomorphisms := by
  unfold smoothUnipotentAffineGroupSchemeProperty
  infer_instance

/-- The category of smooth unipotent affine group schemes of finite type over a field. -/
abbrev SmoothUnipotentAffineGroupSchemeCat (k : Type u) [Field k] :=
  (smoothUnipotentAffineGroupSchemeProperty k).FullSubcategory

/-- A finite-type affine group scheme satisfying the smooth-unipotence property has smooth
structural morphism. -/
theorem smooth_of_smoothUnipotentAffineGroupSchemeProperty
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : smoothUnipotentAffineGroupSchemeProperty k G) :
    Smooth G.obj.obj.X.hom := by
  let E := finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k
  let H := E.inverse.obj G
  let H₀ := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
    (CommHopfAlgCat.{u} k)).op.obj H
  have hH : (smoothCommHopfAlgProperty k).op H₀ :=
    (smoothCommHopfAlgProperty_iff H₀.unop).mpr
      ((smoothUnipotentAffineGroupSchemeProperty_iff k G).mp hG |>.1)
  rw [← smoothAffineGroupSchemeProperty_inverseImage k] at hH
  let eSpec :
      (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι.obj (E.functor.obj H) ≅
        (commHopfAlgCatOpEquivAffineGroupSchemeCat
          (CommRingCat.of k)).functor.obj H₀ :=
    (affineGroupSchemeProperty (CommRingCat.of k)).ι.preimageIso
      ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso k).app H ≪≫
        ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
          (CommRingCat.of k)).app H₀).symm)
  have hEF : smoothAffineGroupSchemeProperty (CommRingCat.of k)
      ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι.obj (E.functor.obj H)) :=
    (smoothAffineGroupSchemeProperty (CommRingCat.of k)).prop_of_iso eSpec.symm hH
  exact (smoothAffineGroupSchemeProperty_iff (CommRingCat.of k) G.obj).mp <|
    (smoothAffineGroupSchemeProperty (CommRingCat.of k)).prop_of_iso
      ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι.mapIso
        (E.counitIso.app G)) hEF

/-- Objects of `SmoothUnipotentAffineGroupSchemeCat k` have smooth structural morphism. -/
instance (k : Type u) [Field k] (G : SmoothUnipotentAffineGroupSchemeCat k) :
    Smooth G.obj.obj.obj.X.hom :=
  smooth_of_smoothUnipotentAffineGroupSchemeProperty k G.obj G.property

/-- Under the finite-type affine Hopf/group-scheme anti-equivalence, the inverse image of smooth
unipotence on group schemes is smooth unipotence of coordinate Hopf algebras. -/
theorem smoothUnipotentAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k] :
    (smoothUnipotentAffineGroupSchemeProperty k).inverseImage
        (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor =
      (smoothUnipotentCommHopfAlgProperty k).op := by
  ext H
  exact ((smoothUnipotentCommHopfAlgProperty k).op.prop_iff_of_iso
    ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).unitIso.app H)).symm

/-- `Spec` restricts to an anti-equivalence from smooth unipotent finite-type commutative Hopf
algebras to smooth unipotent affine group schemes. -/
noncomputable def
    smoothUnipotentCommHopfAlgCatOpEquivSmoothUnipotentAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (SmoothUnipotentCommHopfAlgCat.{u, u} k)ᵒᵖ ≌
      SmoothUnipotentAffineGroupSchemeCat k :=
  (ObjectProperty.opEquivalence (smoothUnipotentCommHopfAlgProperty k)).symm.trans <|
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).congrFullSubcategory
      (smoothUnipotentAffineGroupSchemeProperty_inverseImage k)

/-- The forward smooth-unipotent anti-equivalence followed by the inclusions into finite-type
affine group schemes is the finite-type anti-equivalence after forgetting smooth unipotence.

This private isomorphism isolates the representation boundary of `opEquivalence`, `trans`, and
`congrFullSubcategory` from the public `Spec` compatibility isomorphism below. -/
private noncomputable def
    smoothUnipotentCommHopfAlgCatOpEquivSmoothUnipotentAffineGroupSchemeCatFunctorCompιIso
    (k : Type u) [Field k] :
    (smoothUnipotentCommHopfAlgCatOpEquivSmoothUnipotentAffineGroupSchemeCat k).functor ⋙
        (smoothUnipotentAffineGroupSchemeProperty k).ι ≅
      (forget₂ (SmoothUnipotentCommHopfAlgCat.{u, u} k)
          (FiniteTypeCommHopfAlgCat.{u, u} k)).op ⋙
        (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor :=
  Iso.refl _

/-- The forward smooth-unipotent anti-equivalence, followed by the inclusions into finite-type
affine group schemes and affine group schemes, is Mathlib's `hopfSpec` after forgetting the
smooth-unipotent and finite-type proofs. This is the computation interface for the restricted
equivalence. -/
noncomputable def
    smoothUnipotentCommHopfAlgCatOpEquivSmoothUnipotentAffineGroupSchemeCat.functorCompιIso
    (k : Type u) [Field k] :
    (smoothUnipotentCommHopfAlgCatOpEquivSmoothUnipotentAffineGroupSchemeCat k).functor ⋙
          (smoothUnipotentAffineGroupSchemeProperty k).ι ⋙
          (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι ≅
      (forget₂ (SmoothUnipotentCommHopfAlgCat.{u, u} k)
          (FiniteTypeCommHopfAlgCat.{u, u} k)).op ⋙
        (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (CommHopfAlgCat.{u} k)).op ⋙ hopfSpec (CommRingCat.of k) :=
  Functor.isoWhiskerRight
      (smoothUnipotentCommHopfAlgCatOpEquivSmoothUnipotentAffineGroupSchemeCatFunctorCompιIso k)
      ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (SmoothUnipotentCommHopfAlgCat.{u, u} k)
        (FiniteTypeCommHopfAlgCat.{u, u} k)).op
      (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso k)

end TauCeti
