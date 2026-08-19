/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Radical.Basic

/-!
# Semisimple affine group schemes

This file transports semisimplicity from finite-type commutative Hopf algebras to affine group
schemes of finite type over a field. The coordinate-ring predicate says that the group is smooth
and geometrically connected and that every connected normal smooth solvable closed subgroup of
its geometric fibre is trivial. The resulting full subcategory is anti-equivalent to semisimple
finite-type commutative Hopf algebras.

The formulation uses the universal property of a trivial geometric radical. It does not assume
that a maximal solvable normal subgroup has already been constructed. Its triviality requirement
ranges over connected normal smooth solvable subgroup schemes; nonsmooth subgroup schemes are not
constrained, while the ambient finite-type affine-group-scheme category still includes nonsmooth
objects. Bundled semisimple objects carry smooth and geometrically connected structural-morphism
instances.

## Main declarations

* `TauCeti.semisimpleAffineGroupSchemeProperty`: semisimplicity for finite-type affine group
  schemes over a field.
* `TauCeti.semisimpleAffineGroupSchemeProperty_iff`: its coordinate-ring characterization.
* `TauCeti.SemisimpleAffineGroupSchemeCat`: the corresponding full subcategory.
* `TauCeti.smooth_of_semisimpleAffineGroupSchemeProperty` and
  `TauCeti.geometricallyConnected_of_semisimpleAffineGroupSchemeProperty`: the scheme-side
  smoothness and geometric-connectedness eliminators.
* `TauCeti.semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat`: the restricted affine
  Hopf/group-scheme anti-equivalence.
* `TauCeti.semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat.functorCompιIso`: its
  computation isomorphism after forgetting to affine group schemes.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.46 and 21.10.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.

The formal organization follows `TauCeti.AlgebraicGeometry.AffineGroupScheme.Unipotent`. This
advances Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap by keeping
the coordinate-Hopf and affine-group-scheme models synchronized. Construction of the geometric
radical and identification of this predicate with its triviality remain downstream.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- The candidate subgroup property used in the generic scheme-side packaging of
semisimplicity. -/
private abbrev semisimpleGeometricSubgroupProperty (k : Type u) [Field k] :=
  ((smoothCommHopfAlgProperty (AlgebraicClosure k)) ⊓
    geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)).inverseImage
      (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
        (CommHopfAlgCat.{u} (AlgebraicClosure k)))

/-- The object property selecting semisimple affine group schemes of finite type over a field.

The property is transported through the finite-type affine Hopf/group-scheme anti-equivalence.
Thus its normal-subgroup condition is the coordinate-Hopf universal property used by
`semisimpleCommHopfAlgProperty`, presented on the scheme side. -/
def semisimpleAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :=
  geometricNormalSubgroupFreeAffineGroupSchemeProperty k
    (semisimpleGeometricSubgroupProperty k)

/-- A finite-type affine group scheme is semisimple exactly when its coordinate Hopf algebra
satisfies `semisimpleCommHopfAlgProperty`. -/
@[simp]
theorem semisimpleAffineGroupSchemeProperty_iff
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :
    semisimpleAffineGroupSchemeProperty k G ↔
      semisimpleCommHopfAlgProperty k
        ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj G).unop :=
  (geometricNormalSubgroupFreeAffineGroupSchemeProperty_iff k
    (semisimpleGeometricSubgroupProperty k) G).trans <| by
      rw [← semisimpleCommHopfAlgProperty_eq_geometricNormalSubgroupFree]

/-- Semisimplicity of finite-type affine group schemes is invariant under isomorphism. -/
instance (k : Type u) [Field k] :
    (semisimpleAffineGroupSchemeProperty k).IsClosedUnderIsomorphisms := by
  unfold semisimpleAffineGroupSchemeProperty
  infer_instance

/-- The category of semisimple affine group schemes of finite type over a field. -/
abbrev SemisimpleAffineGroupSchemeCat (k : Type u) [Field k] :=
  (semisimpleAffineGroupSchemeProperty k).FullSubcategory

/-- A finite-type affine group scheme satisfying the semisimplicity property has smooth
structural morphism. -/
theorem smooth_of_semisimpleAffineGroupSchemeProperty
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : semisimpleAffineGroupSchemeProperty k G) :
    Smooth G.obj.obj.X.hom := by
  exact smooth_of_geometricNormalSubgroupFreeAffineGroupSchemeProperty k
    (semisimpleGeometricSubgroupProperty k) G hG

/-- Objects of `SemisimpleAffineGroupSchemeCat k` have smooth structural morphism. -/
instance (k : Type u) [Field k] (G : SemisimpleAffineGroupSchemeCat k) :
    Smooth G.obj.obj.obj.X.hom :=
  smooth_of_semisimpleAffineGroupSchemeProperty k G.obj G.property

/-- A finite-type affine group scheme satisfying the semisimplicity property has geometrically
connected structural morphism. -/
theorem geometricallyConnected_of_semisimpleAffineGroupSchemeProperty
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : semisimpleAffineGroupSchemeProperty k G) :
    GeometricallyConnected G.obj.obj.X.hom := by
  exact geometricallyConnected_of_geometricNormalSubgroupFreeAffineGroupSchemeProperty k
    (semisimpleGeometricSubgroupProperty k) G hG

/-- Objects of `SemisimpleAffineGroupSchemeCat k` have geometrically connected structural
morphism. -/
instance (k : Type u) [Field k] (G : SemisimpleAffineGroupSchemeCat k) :
    GeometricallyConnected G.obj.obj.obj.X.hom :=
  geometricallyConnected_of_semisimpleAffineGroupSchemeProperty k G.obj G.property

/-- Under the finite-type affine Hopf/group-scheme anti-equivalence, the inverse image of
semisimplicity on group schemes is semisimplicity of coordinate Hopf algebras. -/
theorem semisimpleAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k] :
    (semisimpleAffineGroupSchemeProperty k).inverseImage
        (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor =
      (semisimpleCommHopfAlgProperty k).op := by
  exact geometricNormalSubgroupFreeAffineGroupSchemeProperty_inverseImage k
    (semisimpleGeometricSubgroupProperty k) (semisimpleCommHopfAlgProperty k)
    (semisimpleCommHopfAlgProperty_eq_geometricNormalSubgroupFree k)

/-- `Spec` restricts to an anti-equivalence from semisimple finite-type commutative Hopf algebras
to semisimple affine group schemes. -/
noncomputable def semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (SemisimpleCommHopfAlgCat.{u} k)ᵒᵖ ≌ SemisimpleAffineGroupSchemeCat k :=
  geometricNormalSubgroupFreeCommHopfAlgCatOpEquivAffineGroupSchemeCat k
    (semisimpleGeometricSubgroupProperty k) (semisimpleCommHopfAlgProperty k)
    (semisimpleCommHopfAlgProperty_eq_geometricNormalSubgroupFree k)

/-- The forward semisimple anti-equivalence, followed by the inclusions into finite-type affine
group schemes and affine group schemes, is Mathlib's `hopfSpec` after forgetting semisimplicity
and finite type. This is the computation interface for the restricted equivalence. -/
noncomputable def
    semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat.functorCompιIso
    (k : Type u) [Field k] :
    (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k).functor ⋙
          (semisimpleAffineGroupSchemeProperty k).ι ⋙
          (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι ≅
      (forget₂ (SemisimpleCommHopfAlgCat.{u} k)
          (FiniteTypeCommHopfAlgCat.{u, u} k)).op ⋙
        (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (CommHopfAlgCat.{u} k)).op ⋙ hopfSpec (CommRingCat.of k) :=
  geometricNormalSubgroupFreeCommHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso k
    (semisimpleGeometricSubgroupProperty k) (semisimpleCommHopfAlgProperty k)
    (semisimpleCommHopfAlgProperty_eq_geometricNormalSubgroupFree k)

end TauCeti
