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

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.

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
The structural morphism of a Hopf spectrum is geometrically reduced if and only if every field
extension of its coordinate algebra is reduced. -/
theorem geometricallyReducedCommHopfAlg_iff_geometricallyReduced_hopfSpec
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyReducedCommHopfAlgProperty k H ↔
      GeometricallyReduced
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) := by
  let : MorphismProperty.RespectsIso @GeometricallyReduced :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [geometricallyReducedCommHopfAlgProperty_iff, hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyReduced) (eqToHom (hopfSpec_obj_X_left k H))]
  rw [GeometricallyReduced.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    let _ : IsReduced ((H : Type u) ⊗[k] K) := h K
    have : IsReduced (Spec (CommRingCat.of ((H : Type u) ⊗[k] K))) := inferInstance
    exact isReduced_of_isOpenImmersion (pullbackSpecIso k H K).hom
  · intro h K _ _
    let _ : IsReduced
        (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k H)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := h K
    have : IsReduced (Spec (CommRingCat.of ((H : Type u) ⊗[k] K))) :=
      isReduced_of_isOpenImmersion (pullbackSpecIso k H K).inv
    exact (affine_isReduced_iff (CommRingCat.of ((H : Type u) ⊗[k] K))).mp this

end

end TauCeti
