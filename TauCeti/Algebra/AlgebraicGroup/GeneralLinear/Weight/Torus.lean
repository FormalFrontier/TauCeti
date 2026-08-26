/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.GeneralLinear
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Relabel
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Weight
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic

/-!
# Weight tori in the general linear group scheme

Let `wt : Fin N → κ → ℤ` be a finite family of characters of the split torus `𝔾ₘ^κ`. Each
character gives a diagonal entry, and together they define a group-scheme morphism

```text
𝔾ₘ^κ → GL_N,     s ↦ diag(∏_j s_j ^ wt(i,j)).
```

This file constructs the morphism by factoring it through the diagonal torus of `GL_N`. On
character lattices, the factorization is the homomorphism sending the `i`-th coordinate character
to `wt i`; contravariance of diagonalizable groups gives the required map of split tori. The
scheme-valued point formula then follows from the existing point comparisons for diagonalizable
groups and the diagonal torus. The file also computes the algebra-valued point map induced by the
weight-torus coordinate morphism and specializes the construction to the rank-one cocharacter
attached to an integer weight on each coordinate.

The construction is the scheme-level realization of `TauCeti.basisWeightTorus`. In particular,
when `wt` is the weight function of a finite free admissible lattice, it supplies the split-torus
morphism in the pinned Chevalley--Demazure construction of Layer 9 of the ReductiveGroups roadmap.
No faithfulness is asserted: an arbitrary weight family may have a common kernel.

## Main declarations

* `TauCeti.GeneralLinear.weightCharacterMap`: the homomorphism on character lattices.
* `TauCeti.GeneralLinear.weightTorusCoordinateMap`: the coordinate Hopf-algebra morphism of the
  represented weight torus.
* `TauCeti.GeneralLinear.weightTorusCoordinateBialgHom`: its direct diagonal-representation form,
  allowing the base ring and torus index to live in different universes.
* `TauCeti.GeneralLinear.weightTorusBaseChangeCoordinateMap`: that morphism base changed along
  `R → K` and transported into the coordinate Hopf algebras built directly over `K`.
* `TauCeti.GeneralLinear.hom_weightTorusBaseChangeCoordinateMap`: the transported map's
  underlying bialgebra morphism is the direct construction over `K`.
* `TauCeti.GeneralLinear.weightTorusBaseChangeCoordinateMap_eq`: the transported map agrees with
  the categorical weight-torus coordinate morphism over `K` when all data share one universe.
* `TauCeti.GeneralLinear.weightTorus`: the represented morphism `𝔾ₘ^κ → GL_N`.
* `TauCeti.GeneralLinear.isClosedImmersion_weightTorus`: spanning weights make the represented
  morphism a closed immersion.
* `TauCeti.GeneralLinear.weightTorusClosedSubgroup`: the resulting closed subgroup scheme.
* `TauCeti.GeneralLinear.schemePointsMulEquiv_weightTorus`: its diagonal matrix on
  scheme-valued points.
* `TauCeti.GeneralLinear.mapPointsFunctor_weightTorusCoordinateMap_app`: the induced map on
  algebra-valued points.
* `TauCeti.GeneralLinear.diagonalTorusCoordinates_pointsMap_weightCharacterMap`: the diagonal
  coordinates of that point map are the prescribed characters.
* `TauCeti.GeneralLinear.weightTorusCoordinateMap_reindex`: composing every weight with a
  permutation of the torus index relabels the weight-torus coordinate map.
* `TauCeti.GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap`: the diagonal
  matrix the weight torus produces on algebra-valued points.
* `TauCeti.GeneralLinear.weightCocharacter`: the cocharacter attached to integer coordinate
  weights.
* `TauCeti.GeneralLinear.mapDomain_weightCocharacter`: its concrete action on algebra-valued
  points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 21.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §§4.4 and 7.1.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.GeneralLinear

universe u v

variable {R κ : Type u} [CommRing R] {N : ℕ}

section DirectCoordinateMap

variable {S : Type u} {sigma : Type v} [CommRing S] [Finite sigma]

/-- The weight-torus coordinate bialgebra morphism constructed directly as a diagonal
representation. Unlike the categorical factorization through `diagonalTorusCoordinateMap`, this
construction permits the base ring and the torus index to live in different universes. -/
noncomputable def weightTorusCoordinateBialgHom (wt : Fin N → sigma → ℤ) :
    coordinateHopfAlgebra S N →ₐc[S]
      MonoidAlgebra S (Multiplicative (sigma →₀ ℤ)) := by
  let _ : Fintype sigma := Fintype.ofFinite sigma
  exact DiagonalizableGroup.diagonalCoordinateMap (Pi.basisFun S (Fin N))
    (fun i => SplitTorus.weightCharacter (wt i))

/-- A generic matrix entry maps under the direct weight-torus bialgebra morphism to the
prescribed character on the diagonal, and to zero off the diagonal. -/
@[simp]
theorem weightTorusCoordinateBialgHom_X (wt : Fin N → sigma → ℤ) (i j : Fin N) :
    weightTorusCoordinateBialgHom (S := S) wt
        (coordinateHopfAlgebraAlgEquiv S N
          (coordinateRingMap S N (MvPolynomial.X (i, j)))) =
      if i = j then
        MonoidAlgebra.single
          (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i))) 1
      else 0 := by
  let _ : Fintype sigma := Fintype.ofFinite sigma
  have hweight : SplitTorus.weightCharacter (wt i) =
      Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i)) := by
    apply Multiplicative.toAdd.injective
    ext k
    simp
  rw [weightTorusCoordinateBialgHom,
    DiagonalizableGroup.diagonalCoordinateMap_X]
  rcases eq_or_ne i j with rfl | hij
  · simpa only [Matrix.diagonal_apply_eq, ↓reduceIte] using congrArg
      (fun g => MonoidAlgebra.single g (1 : S)) hweight
  · simp [hij]

end DirectCoordinateMap

section Construction

variable [Finite κ]

/-- The character-lattice map associated to a family of weights. It sends the standard
character at `i : Fin N` to the finitely supported function corresponding to `wt i`.

Contravariance turns this map into a morphism from the rank-`κ` split torus to the rank-`N`
diagonal torus. -/
noncomputable def weightCharacterMap (wt : Fin N → κ → ℤ) :
    Multiplicative (ULift.{u} (Fin N) →₀ ℤ) →*
      Multiplicative (κ →₀ ℤ) :=
  AddMonoidHom.toMultiplicative
    (Finsupp.linearCombination ℤ fun i : ULift.{u} (Fin N) =>
      Finsupp.equivFunOnFinite.symm (wt i.down)).toAddMonoidHom

/-- The weight character-lattice map takes a standard character to the corresponding weight. -/
@[simp]
theorem weightCharacterMap_ofAdd_single (wt : Fin N → κ → ℤ) (i : Fin N) :
    weightCharacterMap wt
        (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) =
      Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i)) := by
  apply congrArg Multiplicative.ofAdd
  simp

/-- The coordinate Hopf-algebra morphism of the weight torus. It first restricts functions on
`GL_N` to its diagonal torus, then applies the group-algebra map induced by the prescribed
weights. Its direction is opposite to the represented group-scheme morphism. -/
noncomputable def weightTorusCoordinateMap (wt : Fin N → κ → ℤ) :
    coordinateHopfAlgebra R N ⟶
      (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup κ)).obj :=
  diagonalTorusCoordinateMap ≫
    (DiagonalizableGroup.coordinateMap R
      (FGCommGrpCat.ofHom (weightCharacterMap wt))).hom

/-- Applying the weight-torus coordinate map first restricts to the diagonal torus and then
maps each diagonal character along `weightCharacterMap`. -/
theorem weightTorusCoordinateMap_apply (wt : Fin N → κ → ℤ)
    (x : coordinateHopfAlgebra R N) :
    (weightTorusCoordinateMap (R := R) wt).hom x =
      MonoidAlgebra.mapDomainBialgHom R (weightCharacterMap wt)
        ((diagonalTorusCoordinateMap (R := R) (N := N)).hom x) := by
  rw [weightTorusCoordinateMap]
  rfl

/-- A generic matrix entry restricts along the weight torus to the prescribed character on the
diagonal, and to zero off the diagonal. -/
@[simp]
theorem weightTorusCoordinateMap_X (wt : Fin N → κ → ℤ) (i j : Fin N) :
    (weightTorusCoordinateMap (R := R) wt).hom
        (coordinateHopfAlgebraAlgEquiv R N
          (coordinateRingMap R N (MvPolynomial.X (i, j)))) =
      if i = j then
        MonoidAlgebra.single
          (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i))) 1
      else 0 := by
  rw [weightTorusCoordinateMap_apply]
  rw [diagonalTorusCoordinateMap_X]
  split_ifs <;> simp

/-- The categorical weight-torus coordinate map is the direct diagonal-representation
bialgebra morphism when the base ring and torus index live in the same universe. -/
theorem hom_weightTorusCoordinateMap (wt : Fin N → κ → ℤ) :
    (weightTorusCoordinateMap (R := R) wt).hom =
      weightTorusCoordinateBialgHom (S := R) wt := by
  apply coordinateHopfAlgebra_bialgHom_ext R N
  intro i j
  rw [weightTorusCoordinateMap_X, weightTorusCoordinateBialgHom_X]

/-- The group-scheme morphism from a split torus to `GL_N` prescribed by a family of weights.
It factors through the diagonal torus: the `i`-th diagonal entry is the character `wt i`. -/
noncomputable def weightTorus (wt : Fin N → κ → ℤ) :
    SplitTorus.groupScheme R κ ⟶ groupScheme R N :=
  DiagonalizableGroup.groupSchemeMap R
      (FGCommGrpCat.ofHom (weightCharacterMap wt)) ≫
    diagonalTorus

/-- The weight torus is relative spectrum applied contravariantly to its coordinate morphism,
transported across the named presentations of the split torus and `GL_N`. -/
theorem weightTorus_def (wt : Fin N → κ → ℤ) :
    weightTorus (R := R) wt =
      eqToHom (DiagonalizableGroup.groupScheme_def R (SplitTorus.characterGroup κ)) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (weightTorusCoordinateMap wt).op ≫
        eqToHom (groupScheme_def R N).symm := by
  rw [weightTorus, DiagonalizableGroup.groupSchemeMap_def, diagonalTorus_def]
  unfold weightTorusCoordinateMap
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  slice_lhs 2 3 =>
    rw [← (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map_comp]
  rfl

/-- The represented weight torus is the diagonalizable-group representation whose characters
are the prescribed weights. -/
theorem weightTorus_eq_diagonalGroupSchemeHom [Fintype κ] (wt : Fin N → κ → ℤ) :
    weightTorus (R := R) wt =
      DiagonalizableGroup.diagonalGroupSchemeHom
        (SplitTorus.characterGroup κ) (Pi.basisFun R (Fin N)) fun i =>
          SplitTorus.weightCharacter (wt i) := by
  have hcoordinate : weightTorusCoordinateMap (R := R) wt =
      CommHopfAlgCat.ofHom
        (DiagonalizableGroup.diagonalCoordinateMap (Pi.basisFun R (Fin N)) fun i =>
          SplitTorus.weightCharacter (wt i)) := by
    apply _root_.CommHopfAlgCat.hom_ext
    rw [hom_weightTorusCoordinateMap, weightTorusCoordinateBialgHom,
      _root_.CommHopfAlgCat.hom_ofHom]
    apply congrArg (DiagonalizableGroup.diagonalCoordinateMap (Pi.basisFun R (Fin N)))
    funext i
    apply Multiplicative.toAdd.injective
    ext k
    simp [SplitTorus.toAdd_weightCharacter]
  rw [weightTorus_def, DiagonalizableGroup.diagonalGroupSchemeHom_def, hcoordinate]

/-- **A family of weights spanning the character lattice represents the split torus as a closed
subgroup of `GL_N`.** -/
theorem isClosedImmersion_weightTorus (wt : Fin N → κ → ℤ)
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    IsClosedImmersion (weightTorus (R := R) wt).hom.hom.left := by
  let _ : Fintype κ := Fintype.ofFinite κ
  rw [weightTorus_eq_diagonalGroupSchemeHom]
  exact DiagonalizableGroup.isClosedImmersion_diagonalGroupSchemeHom
    (SplitTorus.characterGroup κ) (Pi.basisFun R (Fin N)) _
      (SplitTorus.closure_range_weightCharacter_eq_top wt hwt)

/-- The split torus represented by a spanning family of weights, as a closed subgroup scheme of
`GL_N`. This does not assert maximality in an ambient reductive group. -/
noncomputable def weightTorusClosedSubgroup (wt : Fin N → κ → ℤ)
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    ClosedSubgroupScheme (groupScheme R N) :=
  have _ := isClosedImmersion_weightTorus (R := R) wt hwt
  ClosedSubgroupScheme.mk (weightTorus (R := R) wt)

/-- The underlying subobject of a closed weight torus is represented by its defining weight-torus
morphism. -/
@[simp]
theorem coe_weightTorusClosedSubgroup (wt : Fin N → κ → ℤ)
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    let _ := isClosedImmersion_weightTorus (R := R) wt hwt
    (weightTorusClosedSubgroup (R := R) wt hwt).1 =
      Subobject.mk (weightTorus (R := R) wt) := by
  have _ := isClosedImmersion_weightTorus (R := R) wt hwt
  rw [weightTorusClosedSubgroup]
  exact ClosedSubgroupScheme.coe_mk _

end Construction

section BaseChange

variable [Finite κ]

/-- The base change along `R → K` of the weight-torus coordinate map, transported into the
coordinate Hopf algebras built directly over `K` by `coordinateHopfAlgebraBaseChangeIso` and
`DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso`.

This is a transport of the map over `R`, not a fresh construction over `K`.
`hom_weightTorusBaseChangeCoordinateMap` identifies its underlying bialgebra morphism with the
direct construction over `K`; `weightTorusBaseChangeCoordinateMap_eq` gives the categorical
same-universe form. -/
noncomputable def weightTorusBaseChangeCoordinateMap
    (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
    (wt : Fin N → κ → ℤ) :
    coordinateHopfAlgebra K N ⟶
      (DiagonalizableGroup.coordinateRing K (SplitTorus.characterGroup κ)).obj :=
  (coordinateHopfAlgebraBaseChangeIso R K N).inv ≫
    CommHopfAlgCat.baseChangeMap (weightTorusCoordinateMap (R := R) wt) ≫
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R K
      (SplitTorus.characterGroup κ)).hom

/-- The base-changed weight-torus coordinate map is the stated composite of the two coordinate
base-change isomorphisms with the scalar extension of the map over `R`.

The module system does not expose a definition's body outside its own module, so this is the
form in which downstream files can rewrite with the definition. -/
theorem weightTorusBaseChangeCoordinateMap_def
    (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
    (wt : Fin N → κ → ℤ) :
    weightTorusBaseChangeCoordinateMap R K wt =
      (coordinateHopfAlgebraBaseChangeIso R K N).inv ≫
        CommHopfAlgCat.baseChangeMap (weightTorusCoordinateMap (R := R) wt) ≫
        (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso R K
          (SplitTorus.characterGroup κ)).hom := by
  unfold weightTorusBaseChangeCoordinateMap
  rfl

/-- **Weight-torus coordinate morphisms commute with base change.** The underlying bialgebra
morphism of the transported scalar extension is the direct diagonal-representation morphism
over `K`. This statement allows the extension ring to live in a larger universe. -/
theorem hom_weightTorusBaseChangeCoordinateMap
    (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
    (wt : Fin N → κ → ℤ) :
    (weightTorusBaseChangeCoordinateMap R K wt).hom =
      weightTorusCoordinateBialgHom (S := K) wt := by
  rw [weightTorusBaseChangeCoordinateMap_def]
  apply coordinateHopfAlgebra_bialgHom_ext K N
  intro i j
  rw [coordinateHopfAlgebraBaseChangeMap_X]
  rw [DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso_hom_apply,
    weightTorusCoordinateMap_X, weightTorusCoordinateBialgHom_X]
  split_ifs <;> simp

/-- In one universe, base change of the categorical weight-torus coordinate map agrees with the
categorical map constructed directly over the extension ring. -/
theorem weightTorusBaseChangeCoordinateMap_eq
    (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    (wt : Fin N → κ → ℤ) :
    weightTorusBaseChangeCoordinateMap R K wt =
      weightTorusCoordinateMap (R := K) wt := by
  apply _root_.CommHopfAlgCat.hom_ext
  rw [hom_weightTorusBaseChangeCoordinateMap, hom_weightTorusCoordinateMap]

end BaseChange

section PointsFunctor

/-- Precomposition by the weight-torus coordinate morphism first restricts a character along the
weight map and then embeds the resulting diagonal-torus point into `GL_N`. -/
@[simp]
theorem mapPointsFunctor_weightTorusCoordinateMap_app [Finite κ] (wt : Fin N → κ → ℤ)
    (A : CommAlgCat.{v} R)
    (p : HopfAlgebra.points
      (R := R) (H := MonoidAlgebra R (SplitTorus.characterGroup κ)) A) :
    (CommHopfAlgCat.mapPointsFunctor (weightTorusCoordinateMap wt)).app A p =
      diagonalTorusPoints
        (DiagonalizableGroup.pointsMap (weightCharacterMap wt) p) := by
  rw [weightTorusCoordinateMap, CommHopfAlgCat.mapPointsFunctor_comp_app_apply,
    DiagonalizableGroup.mapPointsFunctor_coordinateMap_app,
    mapPointsFunctor_diagonalTorusCoordinateMap_app, FGCommGrpCat.toMonoidHom_ofHom]

/-- The diagonal coordinates obtained by restricting a split-torus point along a weight family
are the corresponding torus characters. -/
-- Not `@[simp]`: the left-hand side first normalizes through `pointsMap_apply` and
-- `diagonalTorusCoordinates_apply`, so `simpNF` rejects this higher-level equation.
theorem diagonalTorusCoordinates_pointsMap_weightCharacterMap [Fintype κ]
    (wt : Fin N → κ → ℤ)
    (A : CommAlgCat.{v} R)
    (p : HopfAlgebra.points
      (R := R) (H := MonoidAlgebra R (SplitTorus.characterGroup κ)) A)
    (i : Fin N) :
    diagonalTorusCoordinates
        (SplitTorus.pointsMulEquiv
          (DiagonalizableGroup.pointsMap (weightCharacterMap wt) p)) i =
      torusCharacter (SplitTorus.pointsMulEquiv p) (wt i) := by
  rw [diagonalTorusCoordinates_apply,
    SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv,
    DiagonalizableGroup.pointsMulEquiv_pointsMap, freeAbelianCharEquiv_apply,
    MonoidHom.comp_apply, weightCharacterMap_ofAdd_single]
  have hweight : Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i)) =
      SplitTorus.weightCharacter (wt i) := by
    apply Multiplicative.toAdd.injective
    ext j
    simp
  rw [hweight, SplitTorus.apply_weightCharacter,
    ← SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv]

/-- On algebra-valued points, the weight-torus coordinate morphism is the diagonal matrix whose
`i`-th entry is the value of the character `wt i`. -/
theorem pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap [Fintype κ]
    (wt : Fin N → κ → ℤ) (A : CommAlgCat.{v} R)
    (p : HopfAlgebra.points
      (R := R) (H := MonoidAlgebra R (SplitTorus.characterGroup κ)) A) :
    pointsMulEquiv N
        ((CommHopfAlgCat.mapPointsFunctor (weightTorusCoordinateMap (R := R) wt)).app A p) =
      diagGL fun i => torusCharacter (SplitTorus.pointsMulEquiv p) (wt i) := by
  rw [mapPointsFunctor_weightTorusCoordinateMap_app, pointsMulEquiv_diagonalTorusPoints]
  congr 1
  funext i
  exact diagonalTorusCoordinates_pointsMap_weightCharacterMap wt A p i

end PointsFunctor

section Symmetry

variable [Finite κ]

/-- Composing every weight with a permutation `τ` of the torus index relabels the underlying
bialgebra morphism of the weight-torus coordinate map by `τ⁻¹`. -/
theorem hom_weightTorusCoordinateMap_reindex (τ : Equiv.Perm κ) (wt : Fin N → κ → ℤ) :
    (weightTorusCoordinateMap (R := R) fun i => wt i ∘ τ).hom =
      (MonoidAlgebra.mapDomainBialgHom R
        (SplitTorus.characterRelabel τ⁻¹).toMonoidHom).comp
        (weightTorusCoordinateMap (R := R) wt).hom := by
  apply coordinateHopfAlgebra_bialgHom_ext R N
  intro i j
  rw [BialgHom.comp_apply, weightTorusCoordinateMap_X, weightTorusCoordinateMap_X]
  split_ifs with hij
  · rw [MonoidAlgebra.mapDomainBialgHom_single]
    congr 1
    -- The bundled character maps reduce to their `Finsupp` representatives only by definitional
    -- equality; the named relabelling lemma applies after exposing that layer.
    change Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i ∘ τ)) =
      SplitTorus.characterRelabel τ⁻¹
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i)))
    rw [SplitTorus.characterRelabel_ofAdd]
    congr 1
    ext k
    simp [Finsupp.equivMapDomain_apply, Equiv.Perm.inv_def]
  · simp

/-- **Composing every weight with a permutation `τ` of the torus index relabels the represented
weight torus by `τ⁻¹`.** The two weight families present the same subgroup of `GL_N`, differing only
by the automorphism of the split torus which `τ` induces. -/
theorem weightTorusCoordinateMap_reindex (τ : Equiv.Perm κ) (wt : Fin N → κ → ℤ) :
    (weightTorusCoordinateMap (R := R) fun i => wt i ∘ τ) =
      weightTorusCoordinateMap (R := R) wt ≫ SplitTorus.relabelCoordinateMap R τ⁻¹ := by
  apply _root_.CommHopfAlgCat.hom_ext
  rw [_root_.CommHopfAlgCat.hom_comp, SplitTorus.hom_relabelCoordinateMap]
  exact hom_weightTorusCoordinateMap_reindex τ wt

end Symmetry

section WeightCocharacter

/-- The diagonal unit family `i ↦ t ^ w i` attached to integer weights. -/
def weightDiagonalUnits {A : Type v} [CommMonoid A] (w : Fin N → ℤ) :
    Aˣ →* (Fin N → Aˣ) :=
  MonoidHom.pi fun i ↦ zpowGroupHom (w i)

/-- The `i`-th diagonal coordinate of the weight cocharacter is `t ^ w i`. -/
@[simp]
theorem weightDiagonalUnits_apply {A : Type v} [CommMonoid A] (w : Fin N → ℤ)
    (t : Aˣ) (i : Fin N) : weightDiagonalUnits w t i = t ^ w i := by
  rw [weightDiagonalUnits, MonoidHom.pi_apply, zpowGroupHom_apply]

/-- The rank-one character group algebra, presented as Laurent polynomials. -/
private noncomputable def rankOneCharacterBialgEquiv :
    MonoidAlgebra R (Multiplicative (ULift.{u} Unit →₀ ℤ)) ≃ₐc[R]
      LaurentPolynomial R :=
  (MonoidAlgebra.domCongrBialgEquiv R R
      (AddEquiv.toMultiplicative (Finsupp.uniqueAddEquiv (ULift.up ())))).trans
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).symm

/-- The coordinate Hopf-algebra morphism of the cocharacter with weights `w`. -/
private noncomputable def weightCocharacterCoordinateMap (w : Fin N → ℤ) :
    coordinateHopfAlgebra R N ⟶ _root_.CommHopfAlgCat.of R (LaurentPolynomial R) :=
  weightTorusCoordinateMap (R := R) (fun i _ ↦ w i) ≫
    _root_.CommHopfAlgCat.ofHom (rankOneCharacterBialgEquiv (R := R)).toBialgHom

/-- The cocharacter of `GL_N` acting on the `i`-th coordinate with integer weight `w i`. -/
noncomputable def weightCocharacter (w : Fin N → ℤ) :
    coordinateHopfAlgebra R N →ₐc[R] LaurentPolynomial R :=
  (weightCocharacterCoordinateMap (R := R) w).hom

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The weight cocharacter on algebra-valued points. -/
noncomputable def weightCocharacterPoints (w : Fin N → ℤ) :
    WithConv (LaurentPolynomial R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R N →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) N).symm.toMonoidHom.comp <|
    (diagGL (k := A)).comp <|
      (weightDiagonalUnits w).comp
        (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).toMonoidHom

/-- Reading the weight cocharacter as a matrix gives `diag(t ^ w i)`. -/
theorem pointsMulEquiv_weightCocharacterPoints (w : Fin N → ℤ)
    (f : WithConv (LaurentPolynomial R →ₐ[R] A)) :
    pointsMulEquiv N (weightCocharacterPoints w f) =
      diagGL (weightDiagonalUnits w (MultiplicativeGroup.pointsMulEquiv f)) := by
  simp [weightCocharacterPoints]

private theorem rankOneCharacterBialgEquiv_single :
    rankOneCharacterBialgEquiv (R := R)
        (MonoidAlgebra.single
          (Multiplicative.ofAdd (Finsupp.single (ULift.up ()) 1)) 1) =
      LaurentPolynomial.T 1 := by
  rw [rankOneCharacterBialgEquiv]
  apply (AlgEquiv.symm_apply_eq
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toAlgEquiv).mpr
  -- `simp` does not unfold `domCongrBialgEquiv`, so expose its underlying `domCongr`.
  change MonoidAlgebra.domCongr R R
      (AddEquiv.toMultiplicative (Finsupp.uniqueAddEquiv (ULift.up ())))
        (MonoidAlgebra.single
          (Multiplicative.ofAdd (Finsupp.single (ULift.up ()) 1)) 1) =
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toAlgEquiv (LaurentPolynomial.T 1)
  simpa using
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv_single (R := R) (A := R) (M := ℤ) 1 1).symm

private theorem mapPointsFunctor_weightCocharacterCoordinateMap_app (w : Fin N → ℤ)
    (A : CommAlgCat.{v} R) (f : WithConv (LaurentPolynomial R →ₐ[R] A)) :
    (CommHopfAlgCat.mapPointsFunctor
      (weightCocharacterCoordinateMap (R := R) w)).app A f =
      weightCocharacterPoints w f := by
  let q : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} Unit →₀ ℤ)) →ₐ[R] A) :=
    (CommHopfAlgCat.mapPointsFunctor
      (_root_.CommHopfAlgCat.ofHom
        (rankOneCharacterBialgEquiv (R := R)).toBialgHom)).app A f
  rw [weightCocharacterCoordinateMap,
    CommHopfAlgCat.mapPointsFunctor_comp_app_apply]
  -- Normalize the remaining functorial precomposition to the map induced by the weight torus;
  -- the categorical wrapper has no application lemma at this expression.
  change (CommHopfAlgCat.mapPointsFunctor
    (weightTorusCoordinateMap (R := R) (fun i (_ : ULift.{u} Unit) ↦ w i))).app A q = _
  rw [mapPointsFunctor_weightTorusCoordinateMap_app]
  have hq : SplitTorus.pointsMulEquiv q (ULift.up ()) =
      MultiplicativeGroup.pointsMulEquiv f := by
    ext
    rw [SplitTorus.pointsMulEquiv_apply_coe,
      MultiplicativeGroup.pointsMulEquiv_apply,
      MultiplicativeGroup.unitOfPoint_val]
    simp only [q, CommHopfAlgCat.mapPointsFunctor_app_apply,
      WithConv.ofConv_toConv, AlgHom.comp_apply]
    congr 1
    exact rankOneCharacterBialgEquiv_single (R := R)
  apply (pointsMulEquiv (R := R) (A := A) N).injective
  rw [pointsMulEquiv_diagonalTorusPoints,
    pointsMulEquiv_weightCocharacterPoints]
  congr 1
  funext i
  rw [diagonalTorusCoordinates_pointsMap_weightCharacterMap]
  simp [torusCharacter_def, weightDiagonalUnits, hq]

/-- Precomposition by the weight cocharacter sends a Laurent point to its concrete diagonal
weight-cocharacter point. -/
theorem mapDomain_weightCocharacter (w : Fin N → ℤ)
    (f : WithConv (LaurentPolynomial R →ₐ[R] A)) :
    AlgHom.mapDomain (weightCocharacter (R := R) w) f =
      weightCocharacterPoints w f := by
  -- `mapDomain` and the points functor are definitionally the same precomposition here; there is
  -- no bridge lemma for the bundled coordinate morphism.
  change (CommHopfAlgCat.mapPointsFunctor
      (weightCocharacterCoordinateMap (R := R) w)).app (CommAlgCat.of R A) f = _
  exact mapPointsFunctor_weightCocharacterCoordinateMap_app w (CommAlgCat.of R A) f

end WeightCocharacter

variable {A : Type u} [CommRing A] [Algebra R A]

section Finite

variable [Finite κ]

private lemma groupSchemePointMulEquiv_comp_weightTorus (wt : Fin N → κ → ℤ)
    (q : HopfAlgebra.points
      (R := R) (H := MonoidAlgebra R (SplitTorus.characterGroup κ)) (CommAlgCat.of R A)) :
    (DiagonalizableGroup.groupSchemePointsMulEquiv
        (R := R) (A := A) (SplitTorus.characterGroup κ)).symm q ≫
        (weightTorus (R := R) wt).hom.hom =
      groupSchemePointMulEquiv N A
        (diagonalTorusPoints (DiagonalizableGroup.pointsMap (weightCharacterMap wt) q)) := by
  calc
    _ = groupSchemePointMulEquiv N A
        ((CommHopfAlgCat.mapPointsFunctor (weightTorusCoordinateMap wt)).app
          (CommAlgCat.of R A) q) := by
      rw [weightTorus_def]
      apply CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
        (R := R) A (groupScheme_def R N)
          (DiagonalizableGroup.groupScheme_def R (SplitTorus.characterGroup κ))
          (groupSchemePointMulEquiv N A)
          (DiagonalizableGroup.groupSchemePointsMulEquiv
            (R := R) (A := A) (SplitTorus.characterGroup κ)).symm
          (groupSchemePointMulEquiv_apply_left N A)
      exact DiagonalizableGroup.groupSchemePointsMulEquiv_symm_apply_left
        (R := R) (A := A) (SplitTorus.characterGroup κ)
    _ = _ := congrArg (groupSchemePointMulEquiv N A)
      (mapPointsFunctor_weightTorusCoordinateMap_app wt (CommAlgCat.of R A) q)

end Finite

variable [Fintype κ]

/-- On scheme-valued points, the weight torus is the diagonal matrix whose `i`-th diagonal entry
is the value of the character `wt i`. -/
@[simp]
theorem schemePointsMulEquiv_weightTorus (wt : Fin N → κ → ℤ)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (SplitTorus.groupScheme R κ).X) :
    schemePointsMulEquiv N A (p ≫ (weightTorus (R := R) wt).hom.hom) =
      diagGL (fun i => torusCharacter
        (SplitTorus.schemePointsMulEquiv (R := R) (A := A) p) (wt i)) := by
  obtain ⟨q, rfl⟩ := (DiagonalizableGroup.groupSchemePointsMulEquiv
    (R := R) (A := A) (SplitTorus.characterGroup κ)).symm.surjective p
  have hsource : SplitTorus.schemePointsMulEquiv (R := R) (A := A)
      ((DiagonalizableGroup.groupSchemePointsMulEquiv
        (R := R) (A := A) (SplitTorus.characterGroup κ)).symm q) =
      SplitTorus.pointsMulEquiv q := by
    rw [SplitTorus.schemePointsMulEquiv_eq_freeAbelianCharEquiv,
      DiagonalizableGroup.schemePointsMulEquiv_eq_pointsMulEquiv_groupSchemePointsMulEquiv,
      MulEquiv.apply_symm_apply, SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv]
  rw [groupSchemePointMulEquiv_comp_weightTorus,
    schemePointsMulEquiv_groupSchemePointMulEquiv,
    pointsMulEquiv_diagonalTorusPoints, hsource]
  congr 1
  funext i
  exact diagonalTorusCoordinates_pointsMap_weightCharacterMap
    wt (CommAlgCat.of R A) q i

end TauCeti.GeneralLinear
