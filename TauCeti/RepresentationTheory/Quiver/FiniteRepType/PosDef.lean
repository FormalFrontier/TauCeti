/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.TitsForm
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.DimensionVector
public import TauCeti.RepresentationTheory.Quiver.Reflection.Uniqueness

/-!
# A positive definite Tits form forces finite representation type

Let `V` be a finite quiver whose Tits form is positive definite, the numerical side of the ADE
condition in Gabriel's theorem. This file proves that `V` has finite representation type
(`TauCeti.isFiniteRepType_of_titsForm_posDef`), and bounds the number of its indecomposables by the
number of positive roots of the Tits form
(`TauCeti.card_skeleton_indecomposable_le_card_positiveRoots`).

Both come from one map. The dimension vector is constant on isomorphism classes, so it descends to
the skeleton of the finite-dimensional indecomposables as `TauCeti.isoClassDimVector`. That map
lands in the positive roots, by `TauCeti.titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic`,
and is injective, by `TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic`; a
positive definite integral quadratic form takes the value `1` only finitely often, by
`QuadraticMap.PosDef.finite_setOf_apply_eq`, so the skeleton is finite.

No acyclicity hypothesis appears, although both consumed theorems ask for one: a directed cycle
would already contradict positive definiteness, by
`TauCeti.isAcyclic_of_titsForm_posDef`.

This is the affirming half of Gabriel's dichotomy, and the half that the earlier work leaves to be
read off: the two theorems it consumes were proved for their own sake, one saying that a dimension
vector of an indecomposable is a root and one that it determines the indecomposable, and neither
draws the finiteness conclusion. The refuting half, that a quiver outside Dynkin type has infinitely
many indecomposables, is `TauCeti.not_isFiniteRepType_of_infinite` applied to an explicit family, as
in `TauCeti.not_isFiniteRepType_kronecker`.

## Main definitions

* `TauCeti.isoClassDimVector`: the dimension vector of an isomorphism class of finite-dimensional
  indecomposable representations, as an integer vector.

## Main results

* `TauCeti.titsForm_isoClassDimVector_eq_one` and `TauCeti.isoClassDimVector_nonneg`: the dimension
  vector of a class of indecomposables is a positive root of the Tits form.
* `TauCeti.isoClassDimVector_injective`: **the Gabriel injection.** Distinct classes of
  indecomposables have distinct dimension vectors, so `TauCeti.isoClassDimVectorEmbedding` embeds
  the isomorphism classes into the positive roots.
* `TauCeti.isFiniteRepType_of_titsForm_posDef`: **a finite quiver with positive definite Tits form
  has finite representation type.**
* `TauCeti.card_skeleton_indecomposable_le_card_positiveRoots`: it has at most as many
  indecomposables as the Tits form has positive roots.

## Implementation notes

The isomorphism classes are Mathlib's `CategoryTheory.Skeleton` of the full subcategory of
finite-dimensional indecomposable representations, spelled out rather than abbreviated, exactly as
in `TauCeti.IsFiniteRepType` and in `TauCeti.card_skeleton_indecomposable_kronecker`.

`TauCeti.isoClassDimVector` reads its representation off through `CategoryTheory.fromSkeleton`
rather than by a quotient lift. The skeleton is a quotient by definition, but that definition is not
part of its interface; `CategoryTheory.toSkeleton_fromSkeleton_obj` returns the chosen
representative to its own class, which is all a map out of the skeleton needs.

The vertex spaces live in `max v w x` because that is the universe in which the reflection functors
of `TauCeti.RepresentationTheory.Quiver.Reflection.Basic` produce them: the reflected vertex space
at a sink is cut out of a product indexed by the arrows there.

## References

This is the affirming direction of the Gabriel dichotomy `gabriel_finiteRepType_iff` of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, together with the upper bound
of its count milestone. See Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*,
and Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras* I,
Ch. VII.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

variable {k : Type u} {V : Type v} [Field k] [Quiver.{w} V]

section Tits

variable [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]

/-- **The dimension vector of a class of indecomposables is a root of the Tits form**, the class
form of `TauCeti.titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic`. -/
theorem titsForm_isoClassDimVector_eq_one (hpd : (titsForm V).PosDef)
    (X : Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, max v w x} k V ↦ IsFinDim k V M ∧ Indecomposable M))) :
    titsForm V (isoClassDimVector X) = 1 := by
  have hvec : isoClassDimVector X = fun j ↦
      (dimVector ((fromSkeleton _).obj X).obj j : ℤ) :=
    funext (isoClassDimVector_apply X)
  rw [hvec]
  exact titsForm_dimVector_eq_one_of_indecomposable_of_isAcyclic
    (isAcyclic_of_titsForm_posDef hpd) hpd ((fromSkeleton _).obj X).obj
    ((fromSkeleton _).obj X).property.2 ((fromSkeleton _).obj X).property.1

/-- **The Gabriel injection.** Over a finite quiver with positive definite Tits form, two
isomorphism classes of finite-dimensional indecomposable representations with the same dimension
vector coincide. This is `TauCeti.nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic`,
transported to the skeleton. -/
theorem isoClassDimVector_injective (hpd : (titsForm V).PosDef) :
    Function.Injective (isoClassDimVector.{u, v, w, x} (k := k) (V := V)) := by
  intro X Y hXY
  have hd : dimVector ((fromSkeleton _).obj X).obj = dimVector ((fromSkeleton _).obj Y).obj := by
    funext j
    have hj := congrFun hXY j
    rw [isoClassDimVector_apply, isoClassDimVector_apply] at hj
    exact_mod_cast hj
  have hiso := nonempty_iso_of_dimVector_eq_of_indecomposable_of_isAcyclic
    (isAcyclic_of_titsForm_posDef hpd) hpd
    ((fromSkeleton _).obj X).obj ((fromSkeleton _).obj Y).obj
    ((fromSkeleton _).obj X).property.2 ((fromSkeleton _).obj Y).property.2
    ((fromSkeleton _).obj X).property.1 ((fromSkeleton _).obj Y).property.1 hd
  have hcls := (ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso
    (fun M : QuiverRep.{u, v, w, max v w x} k V ↦ IsFinDim k V M ∧ Indecomposable M)
    ((fromSkeleton _).obj X).property ((fromSkeleton _).obj Y).property).mpr hiso
  rwa [toSkeleton_fromSkeleton_obj, toSkeleton_fromSkeleton_obj] at hcls

/-- **The isomorphism classes of finite-dimensional indecomposable representations embed into the
positive roots of the Tits form**, by the dimension vector. This is the injective half of the
Gabriel correspondence, packaged; its surjectivity, that every positive root is the dimension
vector of an indecomposable, is not proved here. -/
noncomputable def isoClassDimVectorEmbedding (hpd : (titsForm V).PosDef) :
    Skeleton (ObjectProperty.FullSubcategory
        (fun M : QuiverRep.{u, v, w, max v w x} k V ↦ IsFinDim k V M ∧ Indecomposable M)) ↪
      {d : V → ℤ // 0 ≤ d ∧ titsForm V d = 1} where
  toFun X := ⟨isoClassDimVector X, isoClassDimVector_nonneg X,
    titsForm_isoClassDimVector_eq_one hpd X⟩
  inj' _ _ h := isoClassDimVector_injective hpd (Subtype.ext_iff.mp h)

/-- The vector underlying the Gabriel injection is the dimension vector of the isomorphism class. -/
@[simp]
theorem coe_isoClassDimVectorEmbedding_apply (hpd : (titsForm V).PosDef)
    (X : Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, max v w x} k V ↦ IsFinDim k V M ∧ Indecomposable M))) :
    ((isoClassDimVectorEmbedding.{u, v, w, x} (k := k) hpd X :
      {d : V → ℤ // 0 ≤ d ∧ titsForm V d = 1}) : V → ℤ) = isoClassDimVector X :=
  (rfl)

/-- **A finite quiver whose Tits form is positive definite has finite representation type.**
This is the affirming direction of Gabriel's dichotomy: the dimension vector embeds the
isomorphism classes of finite-dimensional indecomposables into the roots of the Tits form, of which
a positive definite form has only finitely many.

The refuting direction is `TauCeti.not_isFiniteRepType_of_infinite`, which asks instead for an
infinite family of pairwise non-isomorphic indecomposables. -/
theorem isFiniteRepType_of_titsForm_posDef (hpd : (titsForm V).PosDef) :
    IsFiniteRepType.{u, v, w, max v w x} k V := by
  have : Finite {d : V → ℤ // 0 ≤ d ∧ titsForm V d = 1} :=
    (finite_setOf_nonneg_titsForm_eq_one V hpd).to_subtype
  rw [isFiniteRepType_iff]
  exact Finite.of_injective _ (isoClassDimVectorEmbedding.{u, v, w, x} (k := k) hpd).injective

/-- **A finite quiver with positive definite Tits form has at most as many indecomposable
representations as its Tits form has positive roots.** Gabriel's theorem sharpens this to an
equality, by realizing every positive root; the inequality is what the injection of
`TauCeti.isoClassDimVectorEmbedding` already gives. -/
theorem card_skeleton_indecomposable_le_card_positiveRoots (hpd : (titsForm V).PosDef) :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
        (fun M : QuiverRep.{u, v, w, max v w x} k V ↦ IsFinDim k V M ∧ Indecomposable M))) ≤
      Nat.card {d : V → ℤ // 0 ≤ d ∧ titsForm V d = 1} := by
  have : Finite {d : V → ℤ // 0 ≤ d ∧ titsForm V d = 1} :=
    (finite_setOf_nonneg_titsForm_eq_one V hpd).to_subtype
  exact Nat.card_le_card_of_injective _
    (isoClassDimVectorEmbedding.{u, v, w, x} (k := k) hpd).injective

end Tits

end TauCeti
