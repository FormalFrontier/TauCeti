/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Scheme
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# The type-C standard carrier and its pinned root datum

The full-weight symplectic carrier `TauCeti.SpStd.groupScheme n` is built from the standard
representation of the type-`C_(n+1)` Chevalley generators. Its construction already records the
weight of every numbered raising and lowering generator as a row of the type-`C` Cartan matrix.
This file identifies those weights with the simple roots of the uniform pinned datum
`TauCeti.DynkinType.simplyConnectedRootDatum`.

The distinction matters to downstream consumers. The carrier construction names its roots through
matrix weights, while the CFSG index reaches the pinned datum through its underlying
`TauCeti.DynkinType`. The results below show that the `i`th raising subgroup has the datum's `i`th
simple root and the `i`th lowering subgroup has its negative. They then restate the pointwise and
scheme-point pinning equations using those named roots, so consumers do not have to unfold either
the carrier or the root-datum dispatcher.

Nothing here proves that the carrier is reductive or identifies it with the symplectic group. It
only identifies the already-constructed full-weight torus and numbered root subgroups with the
pinned type-`C` root datum.

## Main results

* `TauCeti.SpStd.rootGeneratorWeight_inr_eq_neg_root_typeCSimpleIndex` identifies the lowering
  generators with the negative simple roots in the directly named type-`C` datum.
* `TauCeti.SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex` and
  `TauCeti.SpStd.rootGeneratorWeight_inr_eq_neg_root_simpleIndex` give both identifications against
  the uniform pinned datum.
* `TauCeti.SpStd.torusPoints_conj_rootSubgroupParam_root_simpleIndex` and its negative-root
  counterpart state the pinning equations on the carrier's matrix-valued points.
* `TauCeti.SpStd.weightTorus_conj_rootSubgroup_root_simpleIndex` and its negative-root counterpart
  state the same equations on scheme points.

## References

The numbering and root datum follow N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate III. The pinning convention follows J. E. Humphreys, *Linear Algebraic Groups*, §§26--27,
and R. W. Carter, *Simple Groups of Lie Type*, §4.4.

This advances the root-subgroup and pinning targets in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is milestone L0, "pinned ambient groups",
of `TauCetiRoadmap/CFSGStatement/README.md`, which reaches this carrier through the pinned datum of
the type-`C` branch of a valid Lie-type index.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.SpStd

open scoped CategoryTheory.MonObj

variable (n : ℕ)

/-! ## The numbered root characters -/

/-- The weight of the `i`th lowering generator is the negative of the `i`th simple root in the
directly named simply connected type-`C_(n+1)` root datum. -/
theorem rootGeneratorWeight_inr_eq_neg_root_typeCSimpleIndex (i : Fin (n + 1)) :
    rootGeneratorWeight n (.inr i) =
      -(DynkinType.typeCSimplyConnectedRootDatum (n + 1)).root
        (DynkinType.typeCSimpleIndex (n + 1) i) := by
  funext j
  rw [rootGeneratorWeight_inr, Pi.neg_apply, DynkinType.root_typeCSimpleIndex]

/-- The weight of the `i`th raising generator is the `i`th simple root of the pinned type-`C_(n+1)`
root datum selected by the uniform Dynkin-type dispatcher. -/
theorem rootGeneratorWeight_inl_eq_root_simpleIndex
    (ht : (DynkinType.C (n + 1)).Valid) (i : Fin (n + 1)) :
    rootGeneratorWeight n (.inl i) =
      ((DynkinType.C (n + 1)).simplyConnectedRootDatum ht).root
        ((DynkinType.C (n + 1)).simpleIndex ht i) := by
  -- The rank of `C (n + 1)` is `n + 1` only up to unfolding, so a direct rewrite by
  -- `root_simpleIndex` cannot construct its dependent motive. Both sides instead compose through
  -- the corresponding row of the Cartan matrix.
  refine Eq.trans ?_ (DynkinType.root_simpleIndex (DynkinType.C (n + 1)) ht i).symm
  rw [DynkinType.cartanMatrix_C]
  funext j
  rw [rootGeneratorWeight_inl]

/-- The weight of the `i`th lowering generator is the negative of the `i`th simple root of the
pinned type-`C_(n+1)` root datum selected by the uniform Dynkin-type dispatcher. -/
theorem rootGeneratorWeight_inr_eq_neg_root_simpleIndex
    (ht : (DynkinType.C (n + 1)).Valid) (i : Fin (n + 1)) :
    rootGeneratorWeight n (.inr i) =
      -((DynkinType.C (n + 1)).simplyConnectedRootDatum ht).root
        ((DynkinType.C (n + 1)).simpleIndex ht i) :=
  -- The direct and dispatcher spellings have definitionally equal character lattices, but their
  -- rank indices block dependent rewriting. This composite transports the already-pinned raising
  -- root equality and then applies negation.
  (rootGeneratorWeight_inr_eq_neg_root_typeCSimpleIndex n i).trans
    (congrArg Neg.neg
      ((rootGeneratorWeight_inl_eq_root n i).symm.trans
        (rootGeneratorWeight_inl_eq_root_simpleIndex n ht i)))

/-! ## Pinning equations on matrix-valued points -/

/-- Conjugation by the full-weight torus rescales the `i`th raising root subgroup through the
`i`th simple root of the pinned type-`C_(n+1)` datum. -/
theorem torusPoints_conj_rootSubgroupParam_root_simpleIndex
    (ht : (DynkinType.C (n + 1)).Valid) (i : Fin (n + 1)) (A : CommAlgCat ℤ)
    (s : Fin (n + 1) → Aˣ) (u : Multiplicative A) :
    torusPoints n A s * rootSubgroupParam n (.inl i) A u * (torusPoints n A s)⁻¹ =
      rootSubgroupParam n (.inl i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              (((DynkinType.C (n + 1)).simplyConnectedRootDatum ht).root
                ((DynkinType.C (n + 1)).simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [torusPoints_conj_rootSubgroupParam,
    rootGeneratorWeight_inl_eq_root_simpleIndex n ht i]

/-- Conjugation by the full-weight torus rescales the `i`th lowering root subgroup through the
negative of the `i`th simple root of the pinned type-`C_(n+1)` datum. -/
theorem torusPoints_conj_rootSubgroupParam_neg_root_simpleIndex
    (ht : (DynkinType.C (n + 1)).Valid) (i : Fin (n + 1)) (A : CommAlgCat ℤ)
    (s : Fin (n + 1) → Aˣ) (u : Multiplicative A) :
    torusPoints n A s * rootSubgroupParam n (.inr i) A u * (torusPoints n A s)⁻¹ =
      rootSubgroupParam n (.inr i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              (-((DynkinType.C (n + 1)).simplyConnectedRootDatum ht).root
                ((DynkinType.C (n + 1)).simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [torusPoints_conj_rootSubgroupParam,
    rootGeneratorWeight_inr_eq_neg_root_simpleIndex n ht i]

/-! ## Pinning equations on scheme points -/

/-- On scheme points, conjugation by the full-weight torus rescales the `i`th raising root subgroup
through the `i`th simple root of the pinned type-`C_(n+1)` datum. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex
    (ht : (DynkinType.C (n + 1)).Valid) (i : Fin (n + 1)) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin (n + 1))).X)
    (u : A) :
    (s ≫ (weightTorus n).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫
          (rootSubgroup n (.inl i)).hom.hom) *
        (s ≫ (weightTorus n).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (((DynkinType.C (n + 1)).simplyConnectedRootDatum ht).root
                ((DynkinType.C (n + 1)).simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup n (.inl i)).hom.hom := by
  rw [weightTorus_conj_rootSubgroup,
    rootGeneratorWeight_inl_eq_root_simpleIndex n ht i]

/-- On scheme points, conjugation by the full-weight torus rescales the `i`th lowering root
subgroup through the negative of the `i`th simple root of the pinned type-`C_(n+1)` datum. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex
    (ht : (DynkinType.C (n + 1)).Valid) (i : Fin (n + 1)) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin (n + 1))).X)
    (u : A) :
    (s ≫ (weightTorus n).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫
          (rootSubgroup n (.inr i)).hom.hom) *
        (s ≫ (weightTorus n).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (-((DynkinType.C (n + 1)).simplyConnectedRootDatum ht).root
                ((DynkinType.C (n + 1)).simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup n (.inr i)).hom.hom := by
  rw [weightTorus_conj_rootSubgroup,
    rootGeneratorWeight_inr_eq_neg_root_simpleIndex n ht i]

end TauCeti.SpStd
