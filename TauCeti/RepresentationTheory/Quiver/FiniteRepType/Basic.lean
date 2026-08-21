/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import TauCeti.CategoryTheory.Skeletal
public import TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional

/-!
# Finite representation type

A quiver has **finite representation type** when it has only finitely many isomorphism classes of
finite-dimensional indecomposable representations. This file defines `TauCeti.IsFiniteRepType`, the
finiteness of the skeleton of the full subcategory of finite-dimensional indecomposables, whose
objects are the representations that are pointwise finite-dimensional
(`TauCeti.IsFinDim`, from `TauCeti.RepresentationTheory.Quiver.Representation.FiniteDimensional`)
and indecomposable; and it proves the criterion by which the property is refuted: an infinite
family of pairwise non-isomorphic finite-dimensional indecomposables.

Both directions of that criterion are proved, because both are used. The refuting direction is what
exhibits a quiver of infinite representation type; the affirming direction is what a quiver of
finite representation type is *for*, namely that any family of pairwise non-isomorphic
finite-dimensional indecomposables is finite, so that "the indecomposables" may be counted.

## Main definitions

* `TauCeti.IsFiniteRepType`: the quiver has finitely many finite-dimensional indecomposables up to
  isomorphism.

## Main results

* `TauCeti.not_isFiniteRepType_of_infinite`: an infinite family of pairwise non-isomorphic
  finite-dimensional indecomposables refutes finite representation type.
* `TauCeti.IsFiniteRepType.finite_of_pairwise_nonisomorphic`: conversely, under finite
  representation type every such family is indexed by a finite type.

## Implementation notes

The definition does not carry `[Finite Q]`. The roadmap pins `IsFiniteRepType` with that instance
binder, to record the intended setting, but nothing in the statement consumes it and an unused
instance argument is a linter error here; a consumer that needs a finite vertex set -- Gabriel's
dichotomy does -- states it where it is used. Dropping it costs nothing: the definition reads the
same, and it stays meaningful over an infinite quiver.

The skeleton is Mathlib's `CategoryTheory.Skeleton`, so `IsFiniteRepType` is a finiteness statement
about an honest type of isomorphism classes rather than about a hand-rolled quotient. The bridge in
both proofs below is `CategoryTheory.ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso`,
that two objects of a full subcategory have the same class in its skeleton exactly when they are
isomorphic in the ambient category.

The two results are stated for a family `M : α → QuiverRep k Q` rather than for a set of
representations: a family is what the worked examples produce -- the loop quiver's family is
indexed by the base field -- and injectivity up to isomorphism is expressed directly on the index
type.

## References

This implements the "finite representation type" item of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, on which its Gabriel
dichotomy and the loop-quiver and Kronecker worked examples are stated.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

variable (k Q) in
/-- **Finite representation type**: the quiver `Q` has only finitely many isomorphism classes of
finite-dimensional indecomposable representations over `k`. It is stated as the finiteness of the
skeleton of the full subcategory they span, so that "isomorphism class" is Mathlib's. -/
def IsFiniteRepType : Prop :=
  Finite (Skeleton (ObjectProperty.FullSubcategory
    (fun M : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q M ∧ Indecomposable M)))

/-- **The elimination and introduction rule for `TauCeti.IsFiniteRepType`**: it is the finiteness
of the skeleton of the full subcategory of finite-dimensional indecomposable representations. -/
@[simp]
theorem isFiniteRepType_iff :
    IsFiniteRepType.{u, v, w, t} k Q ↔ Finite (Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q M ∧ Indecomposable M))) :=
  Iff.rfl

section Criterion

variable {α : Type*} {M : α → QuiverRep.{u, v, w, t} k Q}

/-- The class in the skeleton of a finite-dimensional indecomposable representation. -/
private def toIndecSkeleton {N : QuiverRep.{u, v, w, t} k Q} (hN : IsFinDim k Q N)
    (hN' : Indecomposable N) :
    Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, t} k Q ↦ IsFinDim k Q M ∧ Indecomposable M)) :=
  toSkeleton ⟨N, hN, hN'⟩

/-- Non-isomorphic representations have distinct classes in the skeleton: the inclusion of the full
subcategory of finite-dimensional indecomposables is full and faithful, so an isomorphism there is
an isomorphism of representations. -/
private theorem toIndecSkeleton_injective (hfin : ∀ a, IsFinDim k Q (M a))
    (hind : ∀ a, Indecomposable (M a))
    (hne : ∀ a b, a ≠ b → ¬ Nonempty (M a ≅ M b)) :
    Function.Injective fun a ↦ toIndecSkeleton (hfin a) (hind a) := by
  intro a b hab
  by_contra hne'
  exact hne a b hne'
    ((ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso _ _ _).mp hab)

/-- **An infinite family of pairwise non-isomorphic finite-dimensional indecomposables refutes
finite representation type.** This is how a quiver is shown to have infinite representation type:
exhibit such a family. -/
theorem not_isFiniteRepType_of_infinite [Infinite α] (hfin : ∀ a, IsFinDim k Q (M a))
    (hind : ∀ a, Indecomposable (M a)) (hne : ∀ a b, a ≠ b → ¬ Nonempty (M a ≅ M b)) :
    ¬ IsFiniteRepType.{u, v, w, t} k Q :=
  fun h ↦ (@Finite.of_injective _ _ h _ (toIndecSkeleton_injective hfin hind hne)).false

/-- **Under finite representation type a family of pairwise non-isomorphic finite-dimensional
indecomposables is finite.** This is the counting form of the property: only finitely many
indecomposables are available to be listed. -/
theorem IsFiniteRepType.finite_of_pairwise_nonisomorphic (h : IsFiniteRepType.{u, v, w, t} k Q)
    (hfin : ∀ a, IsFinDim k Q (M a)) (hind : ∀ a, Indecomposable (M a))
    (hne : ∀ a b, a ≠ b → ¬ Nonempty (M a ≅ M b)) : Finite α :=
  @Finite.of_injective _ _ h _ (toIndecSkeleton_injective hfin hind hne)

end Criterion

end TauCeti
