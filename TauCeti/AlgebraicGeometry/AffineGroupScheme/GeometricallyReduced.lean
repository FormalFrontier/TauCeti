/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.CommHopfAlgCat
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Geometric reducedness of affine group schemes

This file compares geometric reducedness of a same-universe commutative Hopf algebra with
Mathlib's scheme-theoretic `GeometricallyReduced` predicate on its Hopf spectrum.

## Main declarations

* `TauCeti.geometricallyReducedCommHopfAlg_iff_geometricallyReduced_hopfSpec`: agreement of the
  coordinate-ring and scheme-theoretic predicates.

## References

* J. S. Milne, *Algebraic Groups* (2017), for the geometric-reducedness terminology.

The comparison follows
`TauCeti.AlgebraicGeometry.AffineGroupScheme.Connected`, especially its Hopf-spectrum
comparison between the coordinate and scheme models.

This advances Layer 2, "Smoothness and dimension tools via `Lie(G)`", of the ReductiveGroups
roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

open AlgebraicGeometry

universe u

noncomputable section

/-- **Geometric reducedness agrees across the affine-group-scheme and coordinate-ring models.**
The structural morphism of a Hopf spectrum is geometrically reduced if and only if its
coordinate algebra stays reduced after every extension `K / k` of the base field, meaning that
`H ⊗[k] K` is reduced for every such `K`. -/
theorem geometricallyReducedCommHopfAlg_iff_geometricallyReduced_hopfSpec
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyReducedCommHopfAlgProperty k H ↔
      GeometricallyReduced
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) := by
  -- This witness is not a global instance, but `cancel_left_of_respectsIso` needs it below.
  let : MorphismProperty.RespectsIso @GeometricallyReduced :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [geometricallyReducedCommHopfAlgProperty_iff, hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyReduced) (eqToHom (hopfSpec_obj_X_left k H))]
  rw [GeometricallyReduced.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  have key (K : Type u) [Field K] [Algebra k K] :
      IsReduced
          (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k H)))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ↔
        IsReduced ((H : Type u) ⊗[k] K) := by
    rw [← affine_isReduced_iff (CommRingCat.of ((H : Type u) ⊗[k] K))]
    exact ⟨fun _ ↦ isReduced_of_isOpenImmersion (pullbackSpecIso k H K).inv,
      fun _ ↦ isReduced_of_isOpenImmersion (pullbackSpecIso k H K).hom⟩
  exact ⟨fun h K _ _ ↦ (key K).mpr (h K), fun h K _ _ ↦ (key K).mp (h K)⟩

end

end TauCeti
