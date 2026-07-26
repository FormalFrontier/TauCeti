/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Functoriality
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat

/-!
# Finite-type diagonalizable groups

The diagonalizable group attached to a commutative group `G` has coordinate Hopf algebra
`R[G]`. It is of finite type over `R` precisely when `G` is finitely generated (over a
nontrivial base). This file packages the forward direction categorically: finitely generated
commutative groups form `FGCommGrpCat`, and the group-algebra construction gives a functor
from this category to finite-type commutative Hopf algebras.

On affine schemes the variance reverses once more under `Spec`, so this covariant coordinate
ring functor is the algebraic side of the contravariant assignment `G ↦ D(G)`. Its morphism
part is `MonoidAlgebra.mapDomainBialgHom`; the existing diagonalizable-group points API shows
that the resulting map of represented groups acts by precomposition on characters.

This advances the reductive-groups roadmap Layer 4 target constructing the anti-equivalence
between finitely generated abelian groups and diagonalizable groups. It supplies the
finite-type source and coordinate-algebra functor needed before essential surjectivity and
full faithfulness can be formulated.

## Main declarations

* `TauCeti.FGCommGrpCat`: the category of finitely generated commutative groups.
* `TauCeti.DiagonalizableGroup.coordinateRing`: `R[G]` as a finite-type commutative Hopf
  algebra.
* `TauCeti.DiagonalizableGroup.coordinateMap`: the coordinate morphism induced by a group
  homomorphism.
* `TauCeti.DiagonalizableGroup.coordinateRingFunctor`: the group-algebra functor from
  finitely generated commutative groups to finite-type commutative Hopf algebras.

## References

The mathematical construction is the diagonalizable-group correspondence in Waterhouse,
*Introduction to Affine Group Schemes*, Chapter 2. The finite-type input is Mathlib's
`MonoidAlgebra.finiteType_of_fg`, and the Hopf morphism is Mathlib's
`MonoidAlgebra.mapDomainBialgHom`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

/-- The object property of being a finitely generated commutative group. -/
@[expose] def fgCommGrpProperty : ObjectProperty CommGrpCat.{v} :=
  fun G => Group.FG G

/-- Membership in the finitely generated commutative-group object property. -/
@[simp]
theorem fgCommGrpProperty_iff (G : CommGrpCat.{v}) :
    fgCommGrpProperty G ↔ Group.FG G :=
  Iff.rfl

/-- The category of finitely generated commutative groups.

This is the source of the coordinate-ring functor for finite-type diagonalizable groups. -/
abbrev FGCommGrpCat :=
  fgCommGrpProperty.FullSubcategory

namespace FGCommGrpCat

/-- The underlying type of a finitely generated commutative group. -/
@[expose, reducible]
def carrier (G : FGCommGrpCat.{v}) : Type v :=
  G.obj

instance : CoeSort FGCommGrpCat.{v} (Type v) :=
  ⟨carrier⟩

attribute [coe] carrier

instance (G : FGCommGrpCat.{v}) : CommGroup G :=
  inferInstanceAs (CommGroup G.obj)

/-- The underlying group of an object of `FGCommGrpCat` is finitely generated. -/
instance (G : FGCommGrpCat.{v}) : Group.FG G :=
  G.property

/-- Construct an object of `FGCommGrpCat` from a finitely generated commutative group. -/
abbrev of (G : Type v) [CommGroup G] [Group.FG G] : FGCommGrpCat.{v} :=
  ⟨CommGrpCat.of G, inferInstanceAs (Group.FG G)⟩

/-- Lift a group homomorphism between finitely generated commutative groups to
`FGCommGrpCat`. -/
abbrev ofHom {G H : Type v} [CommGroup G] [Group.FG G] [CommGroup H] [Group.FG H]
    (φ : G →* H) : of G ⟶ of H :=
  ObjectProperty.homMk (CommGrpCat.ofHom φ)

/-- The group homomorphism underlying a morphism in `FGCommGrpCat`. -/
abbrev toMonoidHom {G H : FGCommGrpCat.{v}} (φ : G ⟶ H) : G →* H :=
  φ.hom.hom

/-- Two morphisms in `FGCommGrpCat` are equal when their underlying group homomorphisms
are equal. -/
@[ext]
theorem hom_ext {G H : FGCommGrpCat.{v}} {φ ψ : G ⟶ H}
    (h : toMonoidHom φ = toMonoidHom ψ) : φ = ψ :=
  ObjectProperty.hom_ext (P := fgCommGrpProperty) (CommGrpCat.hom_ext h)

@[simp]
theorem toMonoidHom_id {G : FGCommGrpCat.{v}} :
    toMonoidHom (𝟙 G) = MonoidHom.id G :=
  rfl

@[simp]
theorem toMonoidHom_comp {G H K : FGCommGrpCat.{v}} (φ : G ⟶ H) (ψ : H ⟶ K) :
    toMonoidHom (φ ≫ ψ) = (toMonoidHom ψ).comp (toMonoidHom φ) :=
  rfl

end FGCommGrpCat

namespace DiagonalizableGroup

variable (R : Type u) [CommRing R]

/-- The coordinate Hopf algebra `R[G]` of the diagonalizable group `D(G)`, bundled as a
finite-type commutative Hopf algebra when `G` is finitely generated. -/
noncomputable abbrev coordinateRing (G : FGCommGrpCat.{v}) :
    FiniteTypeCommHopfAlgCat.{u, max u v} R :=
  FiniteTypeCommHopfAlgCat.of R (MonoidAlgebra R G)

/-- A homomorphism `G → G'` induces the coordinate Hopf-algebra morphism
`R[G] → R[G']` between the corresponding finite-type diagonalizable groups. -/
noncomputable abbrev coordinateMap {G H : FGCommGrpCat.{v}} (φ : G ⟶ H) :
    coordinateRing R G ⟶ coordinateRing R H :=
  FiniteTypeCommHopfAlgCat.ofHom
    (MonoidAlgebra.mapDomainBialgHom R (FGCommGrpCat.toMonoidHom φ))

/-- The bialgebra morphism underlying `coordinateMap φ` is the group-algebra map induced
by the underlying group homomorphism. -/
@[simp]
theorem coordinateMap_toBialgHom {G H : FGCommGrpCat.{v}} (φ : G ⟶ H) :
    FiniteTypeCommHopfAlgCat.toBialgHom (coordinateMap R φ) =
      MonoidAlgebra.mapDomainBialgHom R (FGCommGrpCat.toMonoidHom φ) :=
  rfl

/-- On a group-algebra basis element, `coordinateMap φ` applies `φ` to its index. -/
@[simp]
theorem coordinateMap_single {G H : FGCommGrpCat.{v}} (φ : G ⟶ H) (g : G) (r : R) :
    MonoidAlgebra.mapDomainBialgHom R (FGCommGrpCat.toMonoidHom φ)
        (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (FGCommGrpCat.toMonoidHom φ g) r := by
  simp [MonoidAlgebra.mapDomainBialgHom, MonoidAlgebra.mapDomainAlgHom_apply]

/-- The coordinate-ring construction for finite-type diagonalizable groups.

It is covariant on coordinate Hopf algebras. After applying the contravariant spectrum
functor, it becomes the usual contravariant assignment `G ↦ D(G)`. -/
@[expose] noncomputable def coordinateRingFunctor :
    FGCommGrpCat.{v} ⥤ FiniteTypeCommHopfAlgCat.{u, max u v} R where
  obj := coordinateRing R
  map := coordinateMap R
  map_id G := by
    apply FiniteTypeCommHopfAlgCat.hom_ext
    rw [coordinateMap_toBialgHom, FGCommGrpCat.toMonoidHom_id]
    exact MonoidAlgebra.mapDomainBialgHom_id (R := R) (M := G)
  map_comp φ ψ := by
    apply FiniteTypeCommHopfAlgCat.hom_ext
    rw [coordinateMap_toBialgHom, FGCommGrpCat.toMonoidHom_comp,
      FiniteTypeCommHopfAlgCat.toBialgHom_comp, coordinateMap_toBialgHom,
      coordinateMap_toBialgHom]
    exact MonoidAlgebra.mapDomainBialgHom_comp (R := R)
      (FGCommGrpCat.toMonoidHom ψ) (FGCommGrpCat.toMonoidHom φ)

/-- The object part of `coordinateRingFunctor` is the group algebra `R[G]`. -/
@[simp]
theorem coordinateRingFunctor_obj (G : FGCommGrpCat.{v}) :
    (coordinateRingFunctor R).obj G = coordinateRing R G :=
  rfl

/-- The morphism part of `coordinateRingFunctor` is the group-algebra bialgebra map. -/
@[simp]
theorem coordinateRingFunctor_map {G H : FGCommGrpCat.{v}} (φ : G ⟶ H) :
    (coordinateRingFunctor R).map φ = coordinateMap R φ :=
  rfl

end DiagonalizableGroup

end TauCeti
