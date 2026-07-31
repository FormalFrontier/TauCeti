/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
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
characters. Over an integral domain, every coordinate Hopf-algebra morphism arises uniquely
from a character-group homomorphism, so the coordinate-ring functor is fully faithful.

This advances the reductive-groups roadmap Layer 4 target constructing the anti-equivalence
between finitely generated abelian groups and diagonalizable groups. It supplies the
finite-type source and the coordinate-algebra functor, which is full and faithful over an
integral domain. It does not prove essential surjectivity, construct the scheme-side functor,
or depend on the general Hopf-algebra/affine-group-scheme anti-equivalence.

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
* `TauCeti.DiagonalizableGroup.isGroupLikeElem_iff_eq_single`: group-like elements of a monoid
  algebra over an integral domain are exactly its standard basis elements.
* `TauCeti.DiagonalizableGroup.coordinateMapPreimage`: recover the character-group homomorphism
  inducing a coordinate Hopf-algebra morphism over an integral domain.
* `TauCeti.DiagonalizableGroup.coordinateMap_surjective`: every coordinate Hopf-algebra
  morphism over an integral domain comes from a character-group homomorphism.
* `TauCeti.DiagonalizableGroup.coordinateRingFunctor_faithful`: the coordinate-ring
  functor is faithful over a nontrivial base.
* `TauCeti.DiagonalizableGroup.coordinateRingFunctor_full`: the coordinate-ring functor is
  full over an integral domain.

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

private theorem isGroupLikeElem_single_one {H : Type v} [Monoid H] (h : H) :
    IsGroupLikeElem R (MonoidAlgebra.single h (1 : R)) := by
  constructor
  · simp
  · rw [MonoidAlgebra.comul_single, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def, TensorProduct.map_tmul,
      MonoidAlgebra.lsingle_apply]

/-- Over an integral domain, the group-like elements of a monoid algebra are exactly
the standard basis elements, with a unique basis index. -/
theorem isGroupLikeElem_iff_eq_single [IsDomain R] {H : Type v} [Monoid H]
    (x : MonoidAlgebra R H) :
    IsGroupLikeElem R x ↔ ∃! h : H, x = MonoidAlgebra.single h 1 := by
  constructor
  · intro hx
    have hx_mem : x ∈ Set.range (fun h : H ↦ MonoidAlgebra.single h (1 : R)) := by
      by_contra hx_not_mem
      have hli : LinearIndepOn R id
          (Set.insert x (Set.range (fun h : H ↦ MonoidAlgebra.single h (1 : R)))) :=
        linearIndepOn_isGroupLikeElem.mono (by
          rintro y (rfl | ⟨h, rfl⟩)
          · exact hx
          · exact isGroupLikeElem_single_one R h)
      have hspan := (MonoidAlgebra.basis H R).mem_span x
      change x ∈ Submodule.span R
        (Set.range (fun h : H ↦ MonoidAlgebra.single h (1 : R))) at hspan
      exact hli.notMem_span_of_insert hx_not_mem (by
        simpa using hspan)
    obtain ⟨h, hx_eq⟩ := hx_mem
    refine ⟨h, hx_eq.symm, ?_⟩
    intro h' hx_eq'
    exact MonoidAlgebra.single_left_injective (R := R) (M := H) one_ne_zero
      (hx_eq'.symm.trans hx_eq.symm)
  · rintro ⟨h, rfl, -⟩
    exact isGroupLikeElem_single_one R h

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

/-- The unique index of a group-like element in a monoid algebra over a domain. -/
private noncomputable def groupLikeIndex [IsDomain R] {H : Type v} [Monoid H]
    (x : MonoidAlgebra R H) (hx : IsGroupLikeElem R x) : H :=
  Classical.choose ((isGroupLikeElem_iff_eq_single R x).mp hx)

private theorem eq_single_groupLikeIndex [IsDomain R] {H : Type v} [Monoid H]
    (x : MonoidAlgebra R H) (hx : IsGroupLikeElem R x) :
    x = MonoidAlgebra.single (groupLikeIndex R x hx) 1 :=
  Classical.choose_spec ((isGroupLikeElem_iff_eq_single R x).mp hx) |>.1

/-- Recover the character-group homomorphism that induces a morphism between coordinate
Hopf algebras of finite-type diagonalizable groups over an integral domain. -/
noncomputable def coordinateMapPreimage [IsDomain R] {G H : FGCommGrpCat.{v}}
    (F : coordinateRing R G ⟶ coordinateRing R H) : G ⟶ H :=
  let f := FiniteTypeCommHopfAlgCat.toBialgHom F
  let φ : G → H := fun g ↦
    groupLikeIndex R (f (MonoidAlgebra.single g 1))
      ((isGroupLikeElem_single_one R g).map f)
  have hφ (g : G) :
      f (MonoidAlgebra.single g 1) = MonoidAlgebra.single (φ g) 1 :=
    eq_single_groupLikeIndex R _ _
  FGCommGrpCat.ofHom
    { toFun := φ
      map_one' := by
        apply MonoidAlgebra.single_left_injective (R := R) (M := H) one_ne_zero
        calc
          MonoidAlgebra.single (φ 1) 1 = f (MonoidAlgebra.single 1 1) := (hφ 1).symm
          _ = f 1 := rfl
          _ = 1 := map_one f
          _ = MonoidAlgebra.single 1 1 := rfl
      map_mul' := by
        intro g g'
        apply MonoidAlgebra.single_left_injective (R := R) (M := H) one_ne_zero
        calc
          MonoidAlgebra.single (φ (g * g')) 1 =
              f (MonoidAlgebra.single (g * g') 1) := (hφ (g * g')).symm
          _ = f (MonoidAlgebra.single g 1 * MonoidAlgebra.single g' 1) := by simp
          _ = f (MonoidAlgebra.single g 1) * f (MonoidAlgebra.single g' 1) := map_mul f _ _
          _ = MonoidAlgebra.single (φ g) 1 * MonoidAlgebra.single (φ g') 1 := by
            rw [hφ g, hφ g']
          _ = MonoidAlgebra.single (φ g * φ g') 1 := by simp }

/-- The recovered character-group homomorphism is characterized by the image of each
standard basis element under the coordinate Hopf-algebra morphism. -/
theorem coordinateMapPreimage_single [IsDomain R] {G H : FGCommGrpCat.{v}}
    (F : coordinateRing R G ⟶ coordinateRing R H) (g : G) :
    FiniteTypeCommHopfAlgCat.toBialgHom F (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        (FGCommGrpCat.toMonoidHom (coordinateMapPreimage R F) g) 1 := by
  rw [coordinateMapPreimage]
  change FiniteTypeCommHopfAlgCat.toBialgHom F (MonoidAlgebra.single g 1) =
    MonoidAlgebra.single
      (groupLikeIndex R
        (FiniteTypeCommHopfAlgCat.toBialgHom F (MonoidAlgebra.single g 1))
        ((isGroupLikeElem_single_one R g).map
          (FiniteTypeCommHopfAlgCat.toBialgHom F))) 1
  exact eq_single_groupLikeIndex R _
    ((isGroupLikeElem_single_one R g).map (FiniteTypeCommHopfAlgCat.toBialgHom F))

/-- Applying the coordinate-map construction to the recovered character-group
homomorphism gives the original coordinate Hopf-algebra morphism. -/
theorem coordinateMap_coordinateMapPreimage [IsDomain R] {G H : FGCommGrpCat.{v}}
    (F : coordinateRing R G ⟶ coordinateRing R H) :
    coordinateMap R (coordinateMapPreimage R F) = F := by
  apply FiniteTypeCommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  apply MonoidAlgebra.algHom_ext
  · intro g
    exact (coordinateMap_single R (coordinateMapPreimage R F) g 1).trans
      (coordinateMapPreimage_single R F g).symm
  · ext

/-- Every morphism between coordinate Hopf algebras of finite-type diagonalizable
groups over an integral domain is induced by a character-group homomorphism. -/
theorem coordinateMap_surjective [IsDomain R] {G H : FGCommGrpCat.{v}} :
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

/-- The coordinate-ring functor of finite-type diagonalizable groups is full over an
integral domain. -/
noncomputable instance coordinateRingFunctor_full [IsDomain R] :
    (coordinateRingFunctor R).Full where
  map_surjective := coordinateMap_surjective R

end DiagonalizableGroup

end TauCeti
