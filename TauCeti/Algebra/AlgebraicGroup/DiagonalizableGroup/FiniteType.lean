/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.Category.CommGrpCat.FiniteGeneration

/-!
# Finite-type diagonalizable groups

The diagonalizable group attached to a commutative group `G` has coordinate Hopf algebra
`R[G]`. It is of finite type over `R` precisely when `G` is finitely generated (over a
nontrivial base). This file packages the forward direction categorically: finitely generated
commutative groups form `FGCommGrpCat`, and the group-algebra construction gives a functor
from this category to finite-type commutative Hopf algebras.

On affine schemes the variance reverses once more under `Spec`, so this covariant coordinate
ring functor is the algebraic side of the contravariant assignment `G ↦ D(G)`. Its morphism
part is `MonoidAlgebra.mapDomainBialgHom`; the `DiagonalizableGroup.Functoriality` module
separately shows that the resulting map of represented groups acts by precomposition on
characters.

This advances the reductive-groups roadmap Layer 4 target constructing the anti-equivalence
between finitely generated abelian groups and diagonalizable groups. It supplies the
finite-type source and coordinate-algebra functor needed before essential surjectivity and
full faithfulness can be formulated; it does not construct the scheme-side functor or depend
on the general Hopf-algebra/affine-group-scheme anti-equivalence.

## Main declarations

* `TauCeti.FGCommGrpCat`: the category of finitely generated commutative groups.
* `TauCeti.DiagonalizableGroup.coordinateRing`: `R[G]` as a finite-type commutative Hopf
  algebra.
* `TauCeti.DiagonalizableGroup.coordinateMap`: the coordinate morphism induced by a group
  homomorphism.
* `TauCeti.DiagonalizableGroup.coordinateRingFunctor`: the group-algebra functor from
  finitely generated commutative groups to finite-type commutative Hopf algebras.
* `TauCeti.DiagonalizableGroup.coordinateMap_injective`: coordinate maps remember their
  underlying group homomorphisms over a nontrivial base.
* `TauCeti.DiagonalizableGroup.coordinateRingFunctor_faithful`: the coordinate-ring
  functor is faithful over a nontrivial base.

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
theorem toBialgHom_coordinateMap {G H : FGCommGrpCat.{v}} (φ : G ⟶ H) :
    FiniteTypeCommHopfAlgCat.toBialgHom (coordinateMap R φ) =
      MonoidAlgebra.mapDomainBialgHom R (FGCommGrpCat.toMonoidHom φ) :=
  rfl

/-- The coordinate map sends a group-algebra basis element to the basis element indexed
by its image under the underlying group homomorphism.

This is deliberately not a `simp` lemma: `FiniteTypeCommHopfAlgCat.toBialgHom_ofHom`
already rewrites the left-hand side to `MonoidAlgebra.mapDomainBialgHom`, so `simp` would
never see this form. -/
theorem coordinateMap_single {G H : FGCommGrpCat.{v}} (φ : G ⟶ H) (g : G) (r : R) :
    FiniteTypeCommHopfAlgCat.toBialgHom (coordinateMap R φ) (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (FGCommGrpCat.toMonoidHom φ g) r := by
  rw [toBialgHom_coordinateMap]
  exact MonoidAlgebra.mapDomain_single

/-- Over a nontrivial base ring, the coordinate morphism remembers the group homomorphism
that induced it. -/
theorem coordinateMap_injective [Nontrivial R] {G H : FGCommGrpCat.{v}} :
    Function.Injective (coordinateMap R :
      (G ⟶ H) → (coordinateRing R G ⟶ coordinateRing R H)) := by
  intro φ ψ h
  apply FGCommGrpCat.hom_ext
  ext g
  apply MonoidAlgebra.single_left_injective (R := R) (M := H) one_ne_zero
  calc
    MonoidAlgebra.single (FGCommGrpCat.toMonoidHom φ g) 1 =
        FiniteTypeCommHopfAlgCat.toBialgHom (coordinateMap R φ)
          (MonoidAlgebra.single g 1) := (coordinateMap_single R φ g 1).symm
    _ = FiniteTypeCommHopfAlgCat.toBialgHom (coordinateMap R ψ)
          (MonoidAlgebra.single g 1) := by rw [h]
    _ = MonoidAlgebra.single (FGCommGrpCat.toMonoidHom ψ g) 1 :=
      coordinateMap_single R ψ g 1

/-- The coordinate-ring construction for finite-type diagonalizable groups.

It is covariant on coordinate Hopf algebras. After applying the contravariant spectrum
functor, it becomes the usual contravariant assignment `G ↦ D(G)`. -/
@[expose] noncomputable def coordinateRingFunctor :
    FGCommGrpCat.{v} ⥤ FiniteTypeCommHopfAlgCat.{u, max u v} R where
  obj := coordinateRing R
  map := coordinateMap R
  map_id G := by
    apply FiniteTypeCommHopfAlgCat.hom_ext
    rw [toBialgHom_coordinateMap, FGCommGrpCat.toMonoidHom_id]
    exact MonoidAlgebra.mapDomainBialgHom_id (R := R) (M := G)
  map_comp φ ψ := by
    apply FiniteTypeCommHopfAlgCat.hom_ext
    rw [toBialgHom_coordinateMap, FGCommGrpCat.toMonoidHom_comp,
      FiniteTypeCommHopfAlgCat.toBialgHom_comp, toBialgHom_coordinateMap,
      toBialgHom_coordinateMap]
    exact MonoidAlgebra.mapDomainBialgHom_comp (R := R)
      (FGCommGrpCat.toMonoidHom ψ) (FGCommGrpCat.toMonoidHom φ)

/-- The coordinate-ring functor sends a finitely generated commutative group to its
coordinate Hopf algebra. -/
@[simp]
theorem coordinateRingFunctor_obj (G : FGCommGrpCat.{v}) :
    (coordinateRingFunctor R).obj G = coordinateRing R G :=
  rfl

/-- The coordinate-ring functor sends a group homomorphism to the induced coordinate
Hopf-algebra morphism. -/
@[simp]
theorem coordinateRingFunctor_map {G H : FGCommGrpCat.{v}} (φ : G ⟶ H) :
    (coordinateRingFunctor R).map φ = coordinateMap R φ :=
  rfl

/-- The coordinate-ring functor of finite-type diagonalizable groups is faithful over a
nontrivial base ring. -/
noncomputable instance coordinateRingFunctor_faithful [Nontrivial R] :
    (coordinateRingFunctor R).Faithful where
  map_injective h := coordinateMap_injective R h

end DiagonalizableGroup

end TauCeti
