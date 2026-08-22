/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.Basic

/-!
# Finite-dimensional quiver representations

A representation of a quiver is **pointwise finite-dimensional** when the vector space it puts at
every vertex is finite-dimensional. This file defines that property, `TauCeti.IsFinDim`, and proves
that it transports along an isomorphism of representations.

## Main definitions

* `TauCeti.IsFinDim`: a representation is finite-dimensional at every vertex.

## Main results

* `TauCeti.IsFinDim.of_iso`: pointwise finite-dimensionality transports along an isomorphism.

## Implementation notes

`IsFinDim` is stated vertex by vertex rather than as a single finiteness of the total space: the
category of representations is a functor category, with no ambient module to be finite over, and
over an infinite vertex set the two conditions genuinely differ. Over a finite quiver they agree,
and that is the setting the theory is meant for.

## References

This implements the `IsFinDim` part of the "finite representation type" item of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`; the property itself is
finite-dimensionality of representations, and is used well before that layer's theory.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w t

/-- **Pointwise finite-dimensionality** of a quiver representation: the vector space at every
vertex is finite-dimensional. Over a finite quiver this is total finite-dimensionality, and it is
the finiteness condition under which the indecomposables can be counted; the functor category
itself contains infinite-dimensional objects. -/
def IsFinDim (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]
    (M : QuiverRep.{u, v, w, t} k Q) : Prop :=
  ∀ v : Paths Q, FiniteDimensional k (M.obj v)

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

/-- **The elimination and introduction rule for `TauCeti.IsFinDim`**: it is finite-dimensionality
at every vertex. -/
@[simp]
theorem isFinDim_iff {M : QuiverRep.{u, v, w, t} k Q} :
    IsFinDim k Q M ↔ ∀ v : Paths Q, FiniteDimensional k (M.obj v) :=
  Iff.rfl

/-- Finite-dimensionality at each vertex transports along an isomorphism of representations. -/
theorem IsFinDim.of_iso {M N : QuiverRep.{u, v, w, t} k Q} (h : IsFinDim k Q M) (e : M ≅ N) :
    IsFinDim k Q N := by
  intro v
  have := h v
  exact (e.app v).toLinearEquiv.finiteDimensional

end TauCeti
