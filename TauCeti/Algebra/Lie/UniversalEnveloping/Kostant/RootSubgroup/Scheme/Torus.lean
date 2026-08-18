/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.GeneralLinear
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.WeightTorus
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Weight
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup

/-!
# Diagonal split-torus representations and the Kostant weight torus

A basis `b` of an integral module together with weights `wt` gives a diagonal representation of
the split torus `𝔾ₘ^κ`: a point `s : κ → Aˣ` scales the basis vector `b x` by the value
`∏ⱼ sⱼ ^ wt x j` of its weight character. This file packages that representation as a morphism of
affine group schemes over `ℤ`,

```text
𝔾ₘ^κ ⟶ GLₙ,
```

by reading the weights as characters of the split torus and taking the associated diagonal
representation. When `b` and `wt` are the weight data used by
`TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints`, the two descriptions agree on points of
every value ring, so all the pinning equations proved for that point action — in particular
`kostantTorusPoints_conj_kostantRootSubgroupParam`, the conjugation formula
`t(s) xᵢ(u) t(s)⁻¹ = xᵢ(α(s) u)` — are statements about this morphism.

When the weights span the lattice of exponent vectors the representation is faithful, and the
source torus is then represented as a *closed* subgroup scheme of `GLₙ`. Identifying this closed
subgroup with a maximal torus of a Chevalley group requires the appropriate Kostant lattice,
Cartan weights, and ambient-group construction; those hypotheses are not part of the declarations
in this file.

Integral PBW must still supply the finite free admissible lattices used by the
Chevalley--Demazure construction; the results here apply once such a lattice and weight basis are
given. The representation carrier is universe-zero because the group-scheme reconstruction API
requires the base, coordinate Hopf algebra, and comodule to inhabit the same universe.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.schemePointsMulEquiv_weightTorus_eq_kostantTorusMatrix`:
  composing a scheme-valued torus point with the represented weight torus gives the matrix of the
  existing Kostant torus action.
* `TauCeti.UniversalEnvelopingAlgebra.weightTorusRepresentation`: the diagonal representation
  morphism of affine group schemes `𝔾ₘ^κ ⟶ GLₙ`.
* `TauCeti.UniversalEnvelopingAlgebra.weightTorusClosedSubgroup`: the resulting closed subgroup
  scheme of `GLₙ` when the weights span.

## Main results

* `schemePointsMulEquiv_comp_weightTorusRepresentation_apply`: the named scheme morphism induces
  the diagonal action `kostantTorusPoints` on scheme-valued points.
* `TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_weightTorusRepresentation`: spanning
  weights make the representation a closed immersion.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. S. Milne, *Algebraic Groups* (2017), §12.c.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.UniversalEnvelopingAlgebra

section Matrix

universe v

variable {κ : Type} [Fintype κ]
variable {V : Type v} [AddCommGroup V]
variable (M : AddSubgroup V)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)

variable (A : Type) [CommRing A] [Algebra ℤ A]

/-- Scheme-valued points of the represented weight torus are exactly the matrices of the
pointwise Kostant torus action in the given weight basis. -/
theorem schemePointsMulEquiv_weightTorus_eq_kostantTorusMatrix
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ κ).X) :
    GeneralLinear.schemePointsMulEquiv n A
        (p ≫ (GeneralLinear.weightTorus (R := ℤ) wt).hom.hom) =
      kostantTorusMatrix M b wt
        (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) p) := by
  rw [GeneralLinear.schemePointsMulEquiv_weightTorus, kostantTorusMatrix_apply]

end Matrix

section Representation

variable {κ : Type} {M : Type} [AddCommMonoid M] [Module ℤ M]
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M) (wt : Fin n → κ → ℤ)
variable [Fintype κ]

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

/-- The diagonal representation of a split torus attached to a basis and its weights, as a
morphism of affine group schemes `𝔾ₘ^κ ⟶ GLₙ` over `ℤ`.

It is the diagonal representation of the split torus whose weight characters are the weights of
the basis. -/
noncomputable def weightTorusRepresentation :
    SplitTorus.groupScheme ℤ κ ⟶ GeneralLinear.groupScheme ℤ n :=
  DiagonalizableGroup.diagonalGroupSchemeHom (SplitTorus.characterGroup κ) b fun x =>
    SplitTorus.weightCharacter (wt x)

/-- The weight-torus representation is the general diagonalizable-group representation
specialized to the character lattice of a split torus. -/
theorem weightTorusRepresentation_def :
    weightTorusRepresentation b wt =
      DiagonalizableGroup.diagonalGroupSchemeHom (SplitTorus.characterGroup κ) b fun x =>
        SplitTorus.weightCharacter (wt x) := by
  rw [weightTorusRepresentation]

/-- **A weight basis whose weights span the lattice of exponent vectors presents the split torus
as a closed subgroup of `GLₙ`.** -/
theorem isClosedImmersion_weightTorusRepresentation
    (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    IsClosedImmersion (weightTorusRepresentation b wt).hom.hom.left :=
  DiagonalizableGroup.isClosedImmersion_diagonalGroupSchemeHom (SplitTorus.characterGroup κ) b _
    (SplitTorus.closure_range_weightCharacter_eq_top wt hwt)

/-- The split torus represented by a weight basis with spanning weights, as a closed subgroup
scheme of `GLₙ`. This does not assert maximality in an ambient reductive group. -/
noncomputable def weightTorusClosedSubgroup (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    ClosedSubgroupScheme (GeneralLinear.groupScheme ℤ n) :=
  have _ := isClosedImmersion_weightTorusRepresentation b wt hwt
  ClosedSubgroupScheme.mk (weightTorusRepresentation b wt)

/-- The underlying subobject of the closed weight torus is represented by its defining
closed immersion. -/
@[simp]
theorem coe_weightTorusClosedSubgroup (hwt : Submodule.span ℤ (Set.range wt) = ⊤) :
    let _ := isClosedImmersion_weightTorusRepresentation b wt hwt
    (weightTorusClosedSubgroup b wt hwt).1 =
      Subobject.mk (weightTorusRepresentation b wt) := by
  have _ := isClosedImmersion_weightTorusRepresentation b wt hwt
  rw [weightTorusClosedSubgroup]
  exact ClosedSubgroupScheme.coe_mk _

section Points

variable {V : Type} [AddCommGroup V] [Module ℚ V] (L : AddSubgroup V)
variable (bL : Module.Basis (Fin n) ℤ L)

omit [Module ℚ V] in
private theorem groupSchemePoint_comp_weightTorusRepresentation
    (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ κ).X) :
    p ≫ (weightTorusRepresentation bL wt).hom.hom =
      GeneralLinear.groupSchemePointMulEquiv n A
        (toConv ((DiagonalizableGroup.groupSchemePointsMulEquiv
          (R := ℤ) (A := A) (SplitTorus.characterGroup κ) p).ofConv.comp
            (DiagonalizableGroup.diagonalCoordinateMap bL
              (fun x => SplitTorus.weightCharacter (wt x))).toAlgHom)) := by
  let q := DiagonalizableGroup.groupSchemePointsMulEquiv
    (R := ℤ) (A := A) (SplitTorus.characterGroup κ) p
  let f := CommHopfAlgCat.ofHom (DiagonalizableGroup.diagonalCoordinateMap bL
    (fun x => SplitTorus.weightCharacter (wt x)))
  have hmap := CommHopfAlgCat.mapMulEquiv_mapDomain (CommAlgCat.of ℤ A) f q
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply] at hmap
  apply Over.OverMorphism.ext
  rw [GeneralLinear.groupSchemePointMulEquiv_apply_left, Over.comp_left,
    weightTorusRepresentation_def, DiagonalizableGroup.diagonalGroupSchemeHom_def]
  -- Taking underlying scheme morphisms distributes over this composite definitionally, but the
  -- group-object API has no rewrite lemma exposing that composite.
  rw [show ((eqToHom (DiagonalizableGroup.groupScheme_def ℤ
        (SplitTorus.characterGroup κ)) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map f.op ≫
        eqToHom (GeneralLinear.groupScheme_def ℤ n).symm).hom.hom.left) =
      (eqToHom (DiagonalizableGroup.groupScheme_def ℤ
        (SplitTorus.characterGroup κ))).hom.hom.left ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map f.op).hom.hom.left ≫
        (eqToHom (GeneralLinear.groupScheme_def ℤ n).symm).hom.hom.left from rfl]
  rw [DiagonalizableGroup.eqToHom_hom_hom_left,
    DiagonalizableGroup.eqToHom_hom_hom_left]
  -- Normalize both named group-scheme presentations to their coordinate spectra so that the
  -- contravariance equation `hmap` can be applied to the underlying scheme maps.
  change p.left ≫ eqToHom (DiagonalizableGroup.groupScheme_X_left ℤ
      (SplitTorus.characterGroup κ)) ≫
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map f.op).hom.hom.left ≫
      eqToHom (GeneralLinear.groupScheme_X_left ℤ n).symm =
    (AlgebraicGeometry.Spec.mapMulEquiv
      (toConv (q.ofConv.comp f.hom.toAlgHom))).left ≫
        eqToHom (GeneralLinear.groupScheme_X_left ℤ n).symm
  rw [← Category.assoc p.left,
    DiagonalizableGroup.groupSchemePointsMulEquiv_apply_left_comp]
  change Spec.map (CommRingCat.ofHom q.ofConv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) ≫
        eqToHom (GeneralLinear.groupScheme_X_left ℤ n).symm =
    Spec.map (CommRingCat.ofHom
      ((toConv (q.ofConv.comp f.hom.toAlgHom)).ofConv.toRingHom)) ≫
          eqToHom (GeneralLinear.groupScheme_X_left ℤ n).symm
  have hmapLeft := congrArg Over.Hom.left hmap
  -- The spectrum equivalence and `hopfSpec` display definitionally equal sources through
  -- different wrappers; restate `hmapLeft` with their common coordinate-spectrum types.
  change Spec.map (CommRingCat.ofHom
      ((toConv (q.ofConv.comp f.hom.toAlgHom)).ofConv.toRingHom)) =
    Spec.map (CommRingCat.ofHom q.ofConv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) at hmapLeft
  rw [← Category.assoc, ← hmapLeft]

omit [Module ℚ V] in
/-- **On points, the represented split torus is the original diagonal action.** The matrix of the
point `q` of `𝔾ₘ^κ` in the basis `bL` is the matrix of `kostantTorusPoints` at the coordinate
family of `q`. -/
theorem pointToGeneralLinear_comp_diagonalCoordinateMap_eq_kostantTorusPoints_apply
    (A : Type) [CommRing A]
    (q : WithConv (MonoidAlgebra ℤ (Multiplicative (κ →₀ ℤ)) →ₐ[ℤ] A)) (i j : Fin n) :
    (GeneralLinear.pointToGeneralLinear n
        (toConv (q.ofConv.comp
          (DiagonalizableGroup.diagonalCoordinateMap bL
            (fun x => SplitTorus.weightCharacter (wt x))).toAlgHom)) :
          Matrix (Fin n) (Fin n) A) i j =
      (bL.baseChange A).repr
        ((kostantTorusPoints L bL wt A (SplitTorus.pointsMulEquiv q)).val
          (bL.baseChange A j)) i := by
  classical
  have hmat := DiagonalizableGroup.pointToGeneralLinear_comp_diagonalCoordinateMap bL
    (fun x => SplitTorus.weightCharacter (wt x)) q
  rw [congrFun (congrFun hmat i) j, Module.Basis.baseChange_apply,
    kostantTorusPoints_tmul_basis L bL wt _ 1 j, Module.Basis.baseChange_repr_tmul, bL.repr_self]
  rcases eq_or_ne i j with rfl | hij
  · simp [SplitTorus.charOfPoint_weightCharacter]
  · simp [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]

omit [Module ℚ V] in
/-- On scheme-valued points, the named weight-torus representation induces the diagonal action
`kostantTorusPoints` associated to the same basis and weight data. -/
@[simp]
theorem schemePointsMulEquiv_comp_weightTorusRepresentation_apply
    (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ κ).X) (i j : Fin n) :
    ((GeneralLinear.groupSchemePointMulEquiv n A).symm
        (p ≫ (weightTorusRepresentation bL wt).hom.hom)).ofConv
          (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ n
            (GeneralLinear.coordinateRingMap ℤ n (MvPolynomial.X (i, j)))) =
      (bL.baseChange A).repr
        ((kostantTorusPoints L bL wt A
          (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) p)).val
            (bL.baseChange A j)) i := by
  rw [← GeneralLinear.schemePointsMulEquiv_apply]
  let q := DiagonalizableGroup.groupSchemePointsMulEquiv
    (R := ℤ) (A := A) (SplitTorus.characterGroup κ) p
  have hp := groupSchemePoint_comp_weightTorusRepresentation
    (L := L) (bL := bL) (wt := wt) A p
  have hGL := congrArg (GeneralLinear.schemePointsMulEquiv n A) hp
  have hTorus : SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) p =
      SplitTorus.pointsMulEquiv q := by
    ext x
    exact (SplitTorus.schemePointsMulEquiv_apply_coe p x).trans
      (SplitTorus.pointsMulEquiv_apply_coe q x).symm
  rw [hGL, GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv]
  rw [GeneralLinear.pointsMulEquiv_apply]
  rw [hTorus]
  exact pointToGeneralLinear_comp_diagonalCoordinateMap_eq_kostantTorusPoints_apply
    (L := L) (bL := bL) (wt := wt) A q i j

end Points

end Representation

end TauCeti.UniversalEnvelopingAlgebra
