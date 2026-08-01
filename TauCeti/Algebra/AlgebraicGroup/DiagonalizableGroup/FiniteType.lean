/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.Category.CommGrpCat.FiniteGeneration
public import TauCeti.Algebra.Coalgebra.MonoidAlgebraGroupLike

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
characters. When the base ring has connected prime spectrum, every coordinate Hopf-algebra
morphism arises uniquely from a character-group homomorphism, so the coordinate-ring functor
is fully faithful.

This advances the reductive-groups roadmap Layer 4 target constructing the anti-equivalence
between finitely generated abelian groups and diagonalizable groups. It supplies the
finite-type source and the coordinate-algebra functor, which is full and faithful over a base
with connected prime spectrum. It does not prove essential surjectivity, construct the
scheme-side functor, or depend on the general Hopf-algebra/affine-group-scheme anti-equivalence.

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
* `TauCeti.DiagonalizableGroup.coordinateMapPreimage`: recover the character-group homomorphism
  inducing a coordinate Hopf-algebra morphism over a base with connected prime spectrum.
* `TauCeti.DiagonalizableGroup.coordinateMapPreimage_apply_eq_iff`: characterize the recovered
  homomorphism without exposing its choice-based construction.
* `TauCeti.DiagonalizableGroup.coordinateMap_surjective`: every coordinate Hopf-algebra
  morphism over a base with connected prime spectrum comes from a character-group homomorphism.
* `TauCeti.DiagonalizableGroup.coordinateRingFunctor_faithful`: the coordinate-ring
  functor is faithful over a nontrivial base.
* `TauCeti.DiagonalizableGroup.coordinateRingFunctor_full`: the coordinate-ring functor is
  full over a base with connected prime spectrum.

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

/-- Recover the character-group homomorphism that induces a morphism between coordinate
Hopf algebras of finite-type diagonalizable groups over a base with connected prime
spectrum. -/
noncomputable def coordinateMapPreimage [ConnectedSpace (PrimeSpectrum R)]
    {G H : FGCommGrpCat.{v}}
    (F : coordinateRing R G ⟶ coordinateRing R H) : G ⟶ H :=
  FGCommGrpCat.ofHom <|
    TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage R
      (FiniteTypeCommHopfAlgCat.toBialgHom F)

/-- The recovered character-group homomorphism takes `g` to `h` exactly when the
coordinate Hopf-algebra morphism takes the corresponding standard basis element to
the standard basis element indexed by `h`. -/
theorem coordinateMapPreimage_apply_eq_iff [ConnectedSpace (PrimeSpectrum R)]
    {G H : FGCommGrpCat.{v}} (F : coordinateRing R G ⟶ coordinateRing R H)
    (g : G) (h : H) :
    FGCommGrpCat.toMonoidHom (coordinateMapPreimage R F) g = h ↔
      FiniteTypeCommHopfAlgCat.toBialgHom F (MonoidAlgebra.single g 1) =
        MonoidAlgebra.single h 1 := by
  simpa only [coordinateMapPreimage, FGCommGrpCat.toMonoidHom_ofHom] using
    TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage_apply_eq_iff R
      (FiniteTypeCommHopfAlgCat.toBialgHom F) g h

/-- The recovered character-group homomorphism is characterized by the image of each
standard basis element under the coordinate Hopf-algebra morphism. -/
theorem coordinateMapPreimage_single [ConnectedSpace (PrimeSpectrum R)]
    {G H : FGCommGrpCat.{v}}
    (F : coordinateRing R G ⟶ coordinateRing R H) (g : G) :
    FiniteTypeCommHopfAlgCat.toBialgHom F (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        (FGCommGrpCat.toMonoidHom (coordinateMapPreimage R F) g) 1 := by
  simpa only [coordinateMapPreimage, FGCommGrpCat.toMonoidHom_ofHom] using
    TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage_single R
      (FiniteTypeCommHopfAlgCat.toBialgHom F) g

/-- Applying the coordinate-map construction to the recovered character-group
homomorphism gives the original coordinate Hopf-algebra morphism. -/
@[simp]
theorem coordinateMap_coordinateMapPreimage [ConnectedSpace (PrimeSpectrum R)]
    {G H : FGCommGrpCat.{v}}
    (F : coordinateRing R G ⟶ coordinateRing R H) :
    coordinateMap R (coordinateMapPreimage R F) = F := by
  apply FiniteTypeCommHopfAlgCat.hom_ext
  rw [toBialgHom_coordinateMap]
  simpa only [coordinateMapPreimage, FGCommGrpCat.toMonoidHom_ofHom] using
    TauCeti.MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHomPreimage R
      (FiniteTypeCommHopfAlgCat.toBialgHom F)

/-- Every morphism between coordinate Hopf algebras of finite-type diagonalizable
groups over a base with connected prime spectrum is induced by a character-group
homomorphism. -/
theorem coordinateMap_surjective [ConnectedSpace (PrimeSpectrum R)]
    {G H : FGCommGrpCat.{v}} :
    Function.Surjective (coordinateMap R :
      (G ⟶ H) → (coordinateRing R G ⟶ coordinateRing R H)) := by
  intro F
  exact ⟨coordinateMapPreimage R F, coordinateMap_coordinateMapPreimage R F⟩

/-- Over a nontrivial base ring, the coordinate morphism remembers the group homomorphism
that induced it. -/
theorem coordinateMap_injective [Nontrivial R] {G H : FGCommGrpCat.{v}} :
    Function.Injective (coordinateMap R :
      (G ⟶ H) → (coordinateRing R G ⟶ coordinateRing R H)) := by
  intro φ ψ h
  apply FGCommGrpCat.hom_ext
  apply TauCeti.MonoidAlgebra.mapDomainBialgHom_injective R
  simpa only [← toBialgHom_coordinateMap] using
    congrArg FiniteTypeCommHopfAlgCat.toBialgHom h

/-- Recovering a character-group homomorphism from its coordinate map returns the
original homomorphism. -/
@[simp]
theorem coordinateMapPreimage_coordinateMap [ConnectedSpace (PrimeSpectrum R)]
    {G H : FGCommGrpCat.{v}} (φ : G ⟶ H) :
    coordinateMapPreimage R (coordinateMap R φ) = φ := by
  apply FGCommGrpCat.hom_ext
  simpa only [coordinateMapPreimage, FGCommGrpCat.toMonoidHom_ofHom,
    toBialgHom_coordinateMap] using
    TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage_mapDomainBialgHom R
      (FGCommGrpCat.toMonoidHom φ)

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

/-- The coordinate-ring functor of finite-type diagonalizable groups is full over a
base with connected prime spectrum. -/
noncomputable instance coordinateRingFunctor_full [ConnectedSpace (PrimeSpectrum R)] :
    (coordinateRingFunctor R).Full where
  map_surjective := coordinateMap_surjective R

end DiagonalizableGroup

end TauCeti
