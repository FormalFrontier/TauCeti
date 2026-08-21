/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic

/-!
# Smoothness of commutative Hopf algebras

This file records smoothness of a commutative Hopf algebra over a commutative ring `R` as an
object property. The Hopf algebra structure carries the group law, while `Algebra.Smooth R H`
records smoothness of the coordinate ring separately.

## Main declarations

* `TauCeti.smoothCommHopfAlgProperty`: the object property on `CommHopfAlgCat R` selecting
  objects whose underlying `R`-algebra is smooth.

## References

This is the explicit smoothness predicate requested by `ReductiveGroups/README.md` in
TauCetiRoadmap. Smoothness remains separate from the commutative Hopf algebra category, as
required by the roadmap.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

/-- The object property on commutative Hopf algebras selecting coordinate algebras smooth over
the base ring. -/
def smoothCommHopfAlgProperty (R : Type u) [CommRing R] :
    ObjectProperty (CommHopfAlgCat.{v} R) :=
  fun H => Algebra.Smooth R H

/-- Membership in the smooth commutative-Hopf-algebra object property. -/
@[simp]
lemma smoothCommHopfAlgProperty_iff {R : Type u} [CommRing R]
    (H : CommHopfAlgCat.{v} R) :
    smoothCommHopfAlgProperty R H ↔ Algebra.Smooth R H :=
  Iff.rfl

/-- Smoothness is invariant under isomorphism of commutative Hopf algebras. -/
instance (R : Type u) [CommRing R] :
    (smoothCommHopfAlgProperty R :
      ObjectProperty (CommHopfAlgCat.{v} R)).IsClosedUnderIsomorphisms where
  of_iso e hH := by
    let _ : Algebra.Smooth R _ := hH
    exact Algebra.Smooth.of_equiv (CommHopfAlgCat.ofIso e).toAlgEquiv

end TauCeti
