/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Connected
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth

/-!
# Reductive affine group schemes

This file transports reductivity from finite-type commutative Hopf algebras to affine group
schemes of finite type over a field. The coordinate-ring predicate says that the group is smooth
and geometrically connected and that its geometric fibre has no nontrivial connected normal
smooth unipotent closed subgroup.

The resulting full subcategory is anti-equivalent to reductive finite-type commutative Hopf
algebras (`ReductiveCommHopfAlgCat`). This synchronizes the coordinate-ring and scheme models of
reductive groups, while leaving smoothness and finite type as explicit parts of the predicate
rather than baking them into a monolithic notion of algebraic group.

## Main declarations

* `TauCeti.reductiveAffineGroupSchemeProperty`: reductivity for finite-type affine group schemes
  over a field.
* `TauCeti.reductiveAffineGroupSchemeProperty_iff`: its coordinate-ring characterization.
* `TauCeti.ReductiveAffineGroupSchemeCat`: the corresponding full subcategory.
* `TauCeti.smooth_of_reductiveAffineGroupSchemeProperty` and
  `TauCeti.geometricallyConnected_of_reductiveAffineGroupSchemeProperty`: structural properties
  of reductive affine group schemes, with corresponding instances on the bundled category.
* `TauCeti.reductiveCommHopfAlgCatOpEquivReductiveAffineGroupSchemeCat`: the restricted affine
  Hopf/group-scheme anti-equivalence.
* `TauCeti.reductiveCommHopfAlgCatOpEquivReductiveAffineGroupSchemeCat.functorCompιIso`: its
  `hopfSpec` computation interface.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.46 and 19.b.
* T. A. Springer, *Linear Algebraic Groups*, Chapter 8.
* B. Conrad, *Reductive Group Schemes*, Section 3.
* The categorical restriction and smoothness transport follow the formal pattern in
  `TauCeti.AlgebraicGeometry.AffineGroupScheme.Unipotent`.

This advances Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap. It is
the scheme-side form of the geometric definition and supplies the model needed for the radical,
centre, derived group, central isogenies, and simply connected and adjoint forms.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- The object property selecting reductive affine group schemes of finite type over a field.

The property is transported through the finite-type affine Hopf/group-scheme anti-equivalence.
Thus it presents the coordinate-ring definition on the scheme side without choosing a descended
unipotent radical over the ground field. -/
def reductiveAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :=
  (reductiveCommHopfAlgProperty k).op.inverseImage
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse

/-- A finite-type affine group scheme is reductive exactly when its coordinate Hopf algebra,
supplied by the affine anti-equivalence, is reductive. -/
@[simp]
theorem reductiveAffineGroupSchemeProperty_iff
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :
    reductiveAffineGroupSchemeProperty k G ↔
      reductiveCommHopfAlgProperty k
        ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj G).unop :=
  Iff.rfl

/-- Reductivity of finite-type affine group schemes is invariant under isomorphism. -/
instance (k : Type u) [Field k] :
    (reductiveAffineGroupSchemeProperty k).IsClosedUnderIsomorphisms := by
  unfold reductiveAffineGroupSchemeProperty
  infer_instance

/-- The category of reductive affine group schemes of finite type over a field. -/
abbrev ReductiveAffineGroupSchemeCat (k : Type u) [Field k] :=
  (reductiveAffineGroupSchemeProperty k).FullSubcategory

/-- A finite-type affine group scheme satisfying the reductivity property has smooth structural
morphism. -/
theorem smooth_of_reductiveAffineGroupSchemeProperty
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : reductiveAffineGroupSchemeProperty k G) :
    Smooth G.obj.obj.X.hom := by
  exact (smooth_iff_algebraSmooth_coordinate k G).mpr
    ((reductiveAffineGroupSchemeProperty_iff k G).mp hG).smooth

/-- Objects of `ReductiveAffineGroupSchemeCat k` have smooth structural morphism. -/
instance (k : Type u) [Field k] (G : ReductiveAffineGroupSchemeCat k) :
    Smooth G.obj.obj.obj.X.hom :=
  smooth_of_reductiveAffineGroupSchemeProperty k G.obj G.property

/-- A finite-type affine group scheme satisfying the reductivity property has geometrically
connected structural morphism. -/
theorem geometricallyConnected_of_reductiveAffineGroupSchemeProperty
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k))
    (hG : reductiveAffineGroupSchemeProperty k G) :
    GeometricallyConnected G.obj.obj.X.hom := by
  exact (geometricallyConnected_iff_geometricallyConnected_coordinate k G).mpr
    ((reductiveAffineGroupSchemeProperty_iff k G).mp hG).geometricallyConnected

/-- Objects of `ReductiveAffineGroupSchemeCat k` have geometrically connected structural
morphism. -/
instance (k : Type u) [Field k] (G : ReductiveAffineGroupSchemeCat k) :
    GeometricallyConnected G.obj.obj.obj.X.hom :=
  geometricallyConnected_of_reductiveAffineGroupSchemeProperty k G.obj G.property

/-- Under the finite-type affine Hopf/group-scheme anti-equivalence, the inverse image of
reductivity on group schemes is reductivity of coordinate Hopf algebras. -/
theorem reductiveAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k] :
    (reductiveAffineGroupSchemeProperty k).inverseImage
        (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor =
      (reductiveCommHopfAlgProperty k).op :=
  ObjectProperty.inverseImage_inverse_inverseImage_functor
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k)
    (reductiveCommHopfAlgProperty k).op

/-- `Spec` restricts to an anti-equivalence from reductive finite-type commutative Hopf algebras
to reductive affine group schemes. -/
noncomputable def reductiveCommHopfAlgCatOpEquivReductiveAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (ReductiveCommHopfAlgCat.{u} k)ᵒᵖ ≌ ReductiveAffineGroupSchemeCat k :=
  (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).congrFullSubcategoryOp
    (reductiveCommHopfAlgProperty k) (reductiveAffineGroupSchemeProperty k)
    (reductiveAffineGroupSchemeProperty_inverseImage k)

/-- The forward reductive anti-equivalence, followed by the inclusions into finite-type affine
group schemes and affine group schemes, is Mathlib's `hopfSpec` after forgetting the reductivity
and finite-type proofs. This is the computation interface for the restricted equivalence. -/
noncomputable def
    reductiveCommHopfAlgCatOpEquivReductiveAffineGroupSchemeCat.functorCompιIso
    (k : Type u) [Field k] :
    (reductiveCommHopfAlgCatOpEquivReductiveAffineGroupSchemeCat k).functor ⋙
          (reductiveAffineGroupSchemeProperty k).ι ⋙
          (finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι ≅
      (forget₂ (ReductiveCommHopfAlgCat.{u} k)
          (FiniteTypeCommHopfAlgCat.{u, u} k)).op ⋙
        (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
          (CommHopfAlgCat.{u} k)).op ⋙ hopfSpec (CommRingCat.of k) :=
  congrFullSubcategoryFunctorCompHopfSpecIso k
    (reductiveCommHopfAlgProperty k) (reductiveAffineGroupSchemeProperty k)
    (reductiveAffineGroupSchemeProperty_inverseImage k)

end TauCeti
