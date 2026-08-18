/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Connected
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.FiniteType
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Smooth

/-!
# Semisimple affine group schemes

This file transports semisimplicity from finite-type commutative Hopf algebras to affine group
schemes of finite type over a field. The coordinate-ring predicate says that the group is smooth
and geometrically connected and that every connected normal smooth solvable closed subgroup of
its geometric fibre is trivial. The resulting full subcategory is anti-equivalent to semisimple
finite-type commutative Hopf algebras.

The formulation uses the universal property of a trivial geometric radical. It does not assume
that a maximal solvable normal subgroup has already been constructed, and it does not silently
exclude nonsmooth subgroup schemes from the ambient affine-group-scheme category.

## Main declarations

* `TauCeti.semisimpleAffineGroupSchemeProperty`: semisimplicity for finite-type affine group
  schemes over a field.
* `TauCeti.semisimpleAffineGroupSchemeProperty_iff`: its coordinate-ring characterization.
* `TauCeti.SemisimpleAffineGroupSchemeCat`: the corresponding full subcategory.
* `TauCeti.semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat`: the restricted affine
  Hopf/group-scheme anti-equivalence.

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

/-- The object property selecting semisimple affine group schemes of finite type over a field.

The property is transported through the finite-type affine Hopf/group-scheme anti-equivalence.
Thus its normal-subgroup condition is the coordinate-Hopf universal property used by
`semisimpleCommHopfAlgProperty`, presented on the scheme side. -/
def semisimpleAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :=
  (semisimpleCommHopfAlgProperty k).op.inverseImage
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse

/-- A finite-type affine group scheme is semisimple exactly when its coordinate Hopf algebra is
smooth and geometrically connected and every connected normal smooth solvable closed subgroup of
its geometric fibre is trivial. -/
@[simp]
theorem semisimpleAffineGroupSchemeProperty_iff
    (k : Type u) [Field k]
    (G : FiniteTypeAffineGroupSchemeCat (CommRingCat.of k)) :
    semisimpleAffineGroupSchemeProperty k G ↔
      Algebra.Smooth k
          ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj G).unop ∧
        geometricallyConnectedCommHopfAlgProperty k
          ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj
            G).unop.obj ∧
        ∀ I : HopfIdeal (AlgebraicClosure k)
            (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
              ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj
                G).unop),
          I.IsNormal →
            geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.quotient
                (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
                  ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj
                    G).unop) I).obj →
            Algebra.Smooth (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.quotient
                (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
                  ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj
                    G).unop) I) →
            geometricallySolvablePointsCommHopfAlgProperty (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.quotient
                (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
                  ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj
                    G).unop) I).obj →
            I = HopfIdeal.augmentation (AlgebraicClosure k)
              (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
                ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj
                  G).unop) :=
  semisimpleCommHopfAlgProperty_iff k
    ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).inverse.obj G).unop

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
  let E := finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k
  let H := E.inverse.obj G
  let H₀ := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
    (CommHopfAlgCat.{u} k)).op.obj H
  have hH : (smoothCommHopfAlgProperty k).op H₀ :=
    (smoothCommHopfAlgProperty_iff H₀.unop).mpr
      ((semisimpleAffineGroupSchemeProperty_iff k G).mp hG |>.1)
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
  let E := finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k
  let H := E.inverse.obj G
  let H₀ := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
    (CommHopfAlgCat.{u} k)).op.obj H
  let P : ObjectProperty (Grp (Over (Spec (CommRingCat.of k)))) :=
    fun X ↦ GeometricallyConnected X.X.hom
  let _ : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let _ : P.IsClosedUnderIsomorphisms :=
    { of_iso := fun {X Y} e hX ↦
        (MorphismProperty.over_iso_iff (@GeometricallyConnected)
          ((Grp.forget _).mapIso e)).mp hX }
  let X : Grp (Over (Spec (CommRingCat.of k))) :=
    ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
      (affineGroupSchemeProperty (CommRingCat.of k)).ι).obj (E.functor.obj H)
  let eSpec : X ≅ (hopfSpec (CommRingCat.of k)).obj H₀ :=
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso k).app H
  let eG : X ≅ G.obj.obj :=
    ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
      (affineGroupSchemeProperty (CommRingCat.of k)).ι).mapIso (E.counitIso.app G)
  have hH : geometricallyConnectedCommHopfAlgProperty k H₀.unop :=
    (semisimpleAffineGroupSchemeProperty_iff k G).mp hG |>.2.1
  have hSpec : P ((hopfSpec (CommRingCat.of k)).obj H₀) :=
    (geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec k H₀.unop).mp hH
  exact P.prop_of_iso eG (P.prop_of_iso eSpec.symm hSpec)

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
  ext H
  exact ((semisimpleCommHopfAlgProperty k).op.prop_iff_of_iso
    ((finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).unitIso.app H)).symm

/-- `Spec` restricts to an anti-equivalence from semisimple finite-type commutative Hopf algebras
to semisimple affine group schemes. -/
noncomputable def semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (SemisimpleCommHopfAlgCat.{u} k)ᵒᵖ ≌ SemisimpleAffineGroupSchemeCat k :=
  (ObjectProperty.opEquivalence (semisimpleCommHopfAlgProperty k)).symm.trans <|
    (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).congrFullSubcategory
      (semisimpleAffineGroupSchemeProperty_inverseImage k)

/-- The forward semisimple anti-equivalence followed by the inclusions into finite-type affine
group schemes is the finite-type anti-equivalence after forgetting semisimplicity. -/
private noncomputable def
    semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCatFunctorCompιIso
    (k : Type u) [Field k] :
    (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCat k).functor ⋙
        (semisimpleAffineGroupSchemeProperty k).ι ≅
      (forget₂ (SemisimpleCommHopfAlgCat.{u} k)
          (FiniteTypeCommHopfAlgCat.{u, u} k)).op ⋙
        (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (ObjectProperty.opEquivalence (semisimpleCommHopfAlgProperty k)).symm.functor
      ((semisimpleAffineGroupSchemeProperty k).liftCompιIso _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((semisimpleCommHopfAlgProperty k).op.liftCompιIso _ _)
      (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat k).functor

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
  Functor.isoWhiskerRight
      (semisimpleCommHopfAlgCatOpEquivSemisimpleAffineGroupSchemeCatFunctorCompιIso k)
      ((finiteTypeAffineGroupSchemeProperty (CommRingCat.of k)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (SemisimpleCommHopfAlgCat.{u} k)
        (FiniteTypeCommHopfAlgCat.{u, u} k)).op
      (finiteTypeCommHopfAlgCatOpEquivFiniteTypeAffineGroupSchemeCat.functorCompιIso k)

end TauCeti
