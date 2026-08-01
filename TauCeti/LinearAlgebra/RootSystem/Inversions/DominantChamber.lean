/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Deletion

/-!
# Inversions of a Weyl-group element that preserves dominance

A Weyl-group element carrying a weight interior to the dominant chamber back into the closed
dominant chamber sends no positive root to a negative root, so its inversion set is empty. Since an
element with an empty inversion set is the identity, such an element is the identity: a weight
interior to the dominant chamber is the only point of its Weyl orbit that lies in the closed
dominant chamber, and its stabilizer is trivial.

## Main results

* `TauCeti.mapsTo_posRoots_of_smul_mem_dominantChamber`: such an element maps positive roots to
  positive roots.
* `TauCeti.inversions_eq_empty_of_smul_mem_dominantChamber` and
  `TauCeti.inversions_eq_empty_of_smul_eq_self`: its inversion set is empty.
* `TauCeti.eq_one_of_smul_mem_dominantChamber` and
  `TauCeti.smul_eq_self_of_smul_mem_dominantChamber`: such an element is the identity, so the
  dominant representative of the orbit of an interior weight is unique.
* `TauCeti.eq_one_of_smul_eq_self_of_mem_openDominantChamber`: the Weyl group acts freely on the
  interior of the dominant chamber.

## References

This file proves the uniqueness half of the fundamental-domain item of Layer 4 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, on top of the chamber definitions in
`TauCeti/LinearAlgebra/RootSystem/Chamber.lean` and the identity criterion for inversion sets in
`TauCeti/LinearAlgebra/RootSystem/Inversions/Deletion.lean`. The argument is the one in J. E.
Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. III, §10.
-/

public section

open Set

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) [LinearOrder R] [IsStrictOrderedRing R] (b : P.Base)

variable [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced] {x : M}

/-- A Weyl-group element carrying a weight interior to the dominant chamber back into the closed
dominant chamber keeps every positive root positive. -/
theorem mapsTo_posRoots_of_smul_mem_dominantChamber (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x ∈ dominantChamber P b) :
    MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b) := by
  intro i hi
  by_contra hneg
  rw [not_mem_posRoots_iff_mem_negRoots] at hneg
  -- The coroot functional of the image at the moved weight is the coroot functional of the root
  -- at the original weight, hence positive.
  have h := coroot'_nonpos_of_mem_negRoots P b hw hneg
  rw [RootPairing.coroot'_weylGroupToPerm_smul] at h
  exact absurd h (not_le.mpr (coroot'_pos_of_mem_posRoots P b hx hi))

/-- **A Weyl-group element carrying a weight interior to the dominant chamber back into the closed
dominant chamber has no inversions.** -/
theorem inversions_eq_empty_of_smul_mem_dominantChamber (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x ∈ dominantChamber P b) :
    inversions P b w = ∅ :=
  (inversions_eq_empty_iff P b w).mpr (mapsTo_posRoots_of_smul_mem_dominantChamber P b w hx hw)

/-- A Weyl-group element fixing a weight interior to the dominant chamber has no inversions. -/
theorem inversions_eq_empty_of_smul_eq_self (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x = x) :
    inversions P b w = ∅ :=
  inversions_eq_empty_of_smul_mem_dominantChamber P b w hx
    (by rw [hw]; exact openDominantChamber_subset_dominantChamber P b hx)

/-- **A Weyl-group element carrying a weight interior to the dominant chamber back into the closed
dominant chamber is the identity.** -/
theorem eq_one_of_smul_mem_dominantChamber (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x ∈ dominantChamber P b) : w = 1 :=
  eq_one_of_inversions_eq_empty (inversions_eq_empty_of_smul_mem_dominantChamber P b w hx hw)

/-- **A weight interior to the dominant chamber is the unique dominant weight in its Weyl orbit.**
Together with `TauCeti.exists_mem_dominantChamber`, this is the closed dominant chamber being a
fundamental domain for the Weyl-group action. -/
theorem smul_eq_self_of_smul_mem_dominantChamber (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x ∈ dominantChamber P b) : w • x = x := by
  rw [eq_one_of_smul_mem_dominantChamber P b w hx hw, one_smul]

/-- **The Weyl group acts freely on the interior of the dominant chamber.** -/
theorem eq_one_of_smul_eq_self_of_mem_openDominantChamber (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x = x) : w = 1 :=
  eq_one_of_inversions_eq_empty (inversions_eq_empty_of_smul_eq_self P b w hx hw)

end TauCeti
