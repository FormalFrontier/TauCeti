/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector

/-!
# Dimension vectors of isomorphism classes of indecomposables

The dimension vector is constant on isomorphism classes, so it descends to the skeleton of the
finite-dimensional indecomposable representations as `TauCeti.isoClassDimVector`. This file gives
the generic map and its computation rules; results requiring a positive definite Tits form live in
`TauCeti.RepresentationTheory.Quiver.FiniteRepType.PosDef`.

## Main definitions

* `TauCeti.isoClassDimVector`: the dimension vector of an isomorphism class of finite-dimensional
  indecomposable representations, as an integer vector.

## Main results

* `TauCeti.isoClassDimVector_toSkeleton`: the map sends the class of a representation to that
  representation's dimension vector.
* `TauCeti.isoClassDimVector_nonneg`: the resulting integer vector is nonnegative.

## Implementation notes

`TauCeti.isoClassDimVector` reads its representation through `CategoryTheory.fromSkeleton` rather
than by a quotient lift. The skeleton is a quotient by definition, but that definition is not part
of its interface; `CategoryTheory.toSkeleton_fromSkeleton_obj` returns the chosen representative to
its own class, which is all a map out of the skeleton needs.

The vertex spaces remain in `max v w x`, matching the universe in which the reflection functors
produce them and preserving the common API used by the finite-representation-type results.

## References

This supports the dimension-vector map in the Gabriel correspondence of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w x

variable {k : Type u} {V : Type v} [Field k] [Quiver.{w} V]

/-- **The dimension vector of an isomorphism class of finite-dimensional indecomposable
representations**, as a vector of integers, the shape in which the Tits form reads it.

It is computed on a class by `TauCeti.isoClassDimVector_toSkeleton`; the chosen representative of
the class, supplied by `CategoryTheory.fromSkeleton`, is isomorphic to any other, and the dimension
vector does not see the difference. -/
noncomputable def isoClassDimVector
    (X : Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, max v w x} k V ↦ IsFinDim k V M ∧ Indecomposable M))) :
    V → ℤ :=
  fun j ↦ (dimVector ((fromSkeleton _).obj X).obj j : ℤ)

/-- The dimension vector of a class is read off the representative that
`CategoryTheory.fromSkeleton` chooses. -/
@[simp]
theorem isoClassDimVector_apply
    (X : Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, max v w x} k V ↦ IsFinDim k V M ∧ Indecomposable M)))
    (j : V) :
    isoClassDimVector X j = (dimVector ((fromSkeleton _).obj X).obj j : ℤ) :=
  -- The parentheses keep this an ordinary proof term rather than an exported `rfl` theorem, which
  -- would force `TauCeti.isoClassDimVector` to be `@[expose]`.
  (rfl)

/-- **The dimension vector of a class is the dimension vector of any of its members.** -/
@[simp]
theorem isoClassDimVector_toSkeleton (M : QuiverRep.{u, v, w, max v w x} k V)
    (hfd : ∀ j, FiniteDimensional k (M.obj j)) (hM : Indecomposable M) :
    isoClassDimVector (toSkeleton
        (⟨M, isFinDim_iff.mpr hfd, hM⟩ : ObjectProperty.FullSubcategory
          (fun N : QuiverRep.{u, v, w, max v w x} k V ↦ IsFinDim k V N ∧ Indecomposable N))) =
      fun j ↦ (dimVector M j : ℤ) := by
  have h : dimVector ((fromSkeleton _).obj (toSkeleton
      (⟨M, isFinDim_iff.mpr hfd, hM⟩ : ObjectProperty.FullSubcategory
        (fun N : QuiverRep.{u, v, w, max v w x} k V ↦
          IsFinDim k V N ∧ Indecomposable N)))).obj = dimVector M :=
    dimVector_eq_of_iso ((ObjectProperty.ι _).mapIso (fromSkeletonToSkeletonIso _))
  funext j
  rw [isoClassDimVector_apply]
  exact_mod_cast congrFun h j

/-- The dimension vector of a class of indecomposables is nonnegative, being a vector of
dimensions. -/
theorem isoClassDimVector_nonneg
    (X : Skeleton (ObjectProperty.FullSubcategory
      (fun M : QuiverRep.{u, v, w, max v w x} k V ↦ IsFinDim k V M ∧ Indecomposable M))) :
    0 ≤ isoClassDimVector X :=
  fun _ ↦ Int.natCast_nonneg _

end TauCeti
