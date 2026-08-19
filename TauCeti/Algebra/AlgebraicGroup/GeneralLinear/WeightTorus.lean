/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Weight
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus

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
weight-torus coordinate morphism.

The construction is the scheme-level realization of `TauCeti.basisWeightTorus`. In particular,
when `wt` is the weight function of a finite free admissible lattice, it supplies the split-torus
morphism in the pinned Chevalley--Demazure construction of Layer 9 of the ReductiveGroups roadmap.
No faithfulness is asserted: an arbitrary weight family may have a common kernel.

## Main declarations

* `TauCeti.GeneralLinear.weightCharacterMap`: the homomorphism on character lattices.
* `TauCeti.GeneralLinear.weightTorusCoordinateMap`: the coordinate Hopf-algebra morphism of the
  represented weight torus.
* `TauCeti.GeneralLinear.weightTorus`: the represented morphism `𝔾ₘ^κ → GL_N`.
* `TauCeti.GeneralLinear.schemePointsMulEquiv_weightTorus`: its diagonal matrix on
  scheme-valued points.
* `TauCeti.GeneralLinear.mapPointsFunctor_weightTorusCoordinateMap_app`: the induced map on
  algebra-valued points.
* `TauCeti.GeneralLinear.diagonalTorusCoordinates_pointsMap_weightCharacterMap`: the diagonal
  coordinates of that point map are the prescribed characters.

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

end Construction

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
  rw [weightTorusCoordinateMap, CommHopfAlgCat.mapPointsFunctor_comp,
    CategoryTheory.NatTrans.comp_app]
  -- `rw` cannot see `GrpCat.comp_apply` through the bundled group-hom coercion here.
  erw [GrpCat.comp_apply]
  rw [DiagonalizableGroup.mapPointsFunctor_coordinateMap_app,
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
  rw [diagonalTorusCoordinates_apply]
  apply Units.ext
  rw [SplitTorus.pointsMulEquiv_apply_coe]
  simp only [DiagonalizableGroup.pointsMap_apply, AlgHom.coe_comp, BialgHom.coe_toAlgHom,
    Function.comp_apply, MonoidAlgebra.mapDomainBialgHom_single]
  rw [weightCharacterMap_ofAdd_single, ← DiagonalizableGroup.charOfPoint_apply_coe]
  have hweight : Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i)) =
      SplitTorus.weightCharacter (wt i) := (SplitTorus.weightCharacter_def (wt i)).symm
  rw [hweight]
  rw [SplitTorus.charOfPoint_weightCharacter]

end PointsFunctor

variable {A : Type u} [CommRing A] [Algebra R A]

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
  rw [weightTorus]
  -- Reassociate the two scheme morphisms so the named diagonal-torus point formula applies.
  change schemePointsMulEquiv N A
      ((p ≫ (DiagonalizableGroup.groupSchemeMap R
        (FGCommGrpCat.ofHom (weightCharacterMap wt))).hom.hom) ≫
        diagonalTorus.hom.hom) = _
  rw [schemePointsMulEquiv_diagonalTorus]
  congr 1
  funext i
  let χ : Multiplicative (κ →₀ ℤ) →* Aˣ := DiagonalizableGroup.schemePointsMulEquiv
    (R := R) (A := A) (SplitTorus.characterGroup κ) p
  have hsource : SplitTorus.schemePointsMulEquiv (R := R) (A := A) p =
      freeAbelianCharEquiv χ := by
    funext j
    apply Units.ext
    rw [SplitTorus.schemePointsMulEquiv_apply_coe, freeAbelianCharEquiv_apply,
      DiagonalizableGroup.schemePointsMulEquiv_apply_coe]
    rfl
  have htarget : SplitTorus.schemePointsMulEquiv (R := R) (A := A)
      (p ≫ (DiagonalizableGroup.groupSchemeMap R
        (FGCommGrpCat.ofHom (weightCharacterMap wt))).hom.hom) =
      freeAbelianCharEquiv (χ.comp (weightCharacterMap wt)) := by
    have hmap : DiagonalizableGroup.schemePointsMulEquiv
        (R := R) (A := A) (SplitTorus.characterGroup (ULift.{u} (Fin N)))
        (p ≫ (DiagonalizableGroup.groupSchemeMap R
          (FGCommGrpCat.ofHom (weightCharacterMap wt))).hom.hom) =
        χ.comp (weightCharacterMap wt) := by
      exact DiagonalizableGroup.schemePointsMulEquiv_groupSchemeMap
        (R := R) (A := A) (FGCommGrpCat.ofHom (weightCharacterMap wt)) p
    rw [← hmap]
    funext j
    apply Units.ext
    rw [SplitTorus.schemePointsMulEquiv_apply_coe, freeAbelianCharEquiv_apply,
      DiagonalizableGroup.schemePointsMulEquiv_apply_coe]
    rfl
  rw [diagonalTorusCoordinates_apply, htarget, hsource,
    freeAbelianCharEquiv_apply, MonoidHom.comp_apply, weightCharacterMap_ofAdd_single]
  change χ (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (wt i))) =
    torusCharacter (freeAbelianCharEquiv χ) (wt i)
  conv_lhs =>
    rw [← freeAbelianCharEquiv.symm_apply_apply χ,
      freeAbelianCharEquiv_symm_apply_ofAdd]
  rw [torusCharacter_def, Finsupp.prod_fintype _ _ fun _ => zpow_zero _]
  exact Finset.prod_congr rfl fun j _ => by simp

end TauCeti.GeneralLinear
