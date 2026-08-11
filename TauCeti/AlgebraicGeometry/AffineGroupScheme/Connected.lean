/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Geometric connectedness of affine group schemes

This file compares geometric connectedness of a commutative Hopf algebra with Mathlib's
scheme-theoretic `GeometricallyConnected` predicate on its Hopf spectrum.

## Main declarations

* `TauCeti.geometricallyConnected_hopfSpec_iff`: compatibility of the scheme-theoretic and
  coordinate-ring predicates.
* `TauCeti.geometricallyConnected_hopfSpec_iff_idempotents`: the idempotent characterization of
  geometric connectedness for a Hopf spectrum.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.a.

This is the geometric-connectedness prerequisite for Layer 3, "Identity component and component
group", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

open AlgebraicGeometry

universe u

/-- **Geometric connectedness agrees across the affine-group-scheme and coordinate-ring
models.** The structural morphism of a Hopf spectrum is geometrically connected if and only if
its coordinate algebra is geometrically connected after every field extension. -/
theorem geometricallyConnected_hopfSpec_iff
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    GeometricallyConnected
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) ↔
      geometricallyConnectedCommHopfAlgProperty k H := by
  let : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [geometricallyConnectedCommHopfAlgProperty_iff, hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyConnected) (eqToHom (hopfSpec_obj_X_left k H))]
  rw [GeometricallyConnected.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    exact (pullbackSpecIso k H K).hom.homeomorph.connectedSpace_iff.mp (h K)
  · intro h K _ _
    exact (pullbackSpecIso k H K).hom.homeomorph.connectedSpace_iff.mpr (h K)

/-- The structural morphism of a Hopf spectrum is geometrically connected exactly when every
field extension of its coordinate ring has only zero and one as idempotents. -/
theorem geometricallyConnected_hopfSpec_iff_idempotents
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    GeometricallyConnected
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] (e : (H : Type u) ⊗[k] K),
        IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [geometricallyConnected_hopfSpec_iff,
    geometricallyConnectedCommHopfAlgProperty_iff_idempotents]

end TauCeti
