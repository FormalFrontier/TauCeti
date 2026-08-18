/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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

* `TauCeti.geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec`: compatibility
  of the coordinate-ring and scheme-theoretic predicates.
* `TauCeti.geometricallyConnected_hopfSpec_iff_idempotent_eq_zero_or_one`: the idempotent
  characterization of geometric connectedness for a Hopf spectrum.

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
theorem geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      GeometricallyConnected
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) := by
  -- This witness is not a global instance, but `cancel_left_of_respectsIso` needs it below.
  let : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [geometricallyConnectedCommHopfAlgProperty_iff, hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyConnected) (eqToHom (hopfSpec_obj_X_left k H))]
  rw [GeometricallyConnected.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    exact (pullbackSpecIso k H K).hom.homeomorph.connectedSpace_iff.mpr (h K)
  · intro h K _ _
    exact (pullbackSpecIso k H K).hom.homeomorph.connectedSpace_iff.mp (h K)

/-- The structural morphism of a Hopf spectrum is geometrically connected exactly when, after
every extension `K / k` of the base field, every idempotent of `H ⊗[k] K` is zero or one. -/
theorem geometricallyConnected_hopfSpec_iff_idempotent_eq_zero_or_one
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    GeometricallyConnected
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] (e : (H : Type u) ⊗[k] K),
        IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [← geometricallyConnectedCommHopfAlg_iff_geometricallyConnected_hopfSpec,
    geometricallyConnectedCommHopfAlgProperty_iff_idempotent_eq_zero_or_one]

end TauCeti
