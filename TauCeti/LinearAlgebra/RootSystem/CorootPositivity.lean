/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Basic

/-!
# Positivity on the coroot side, and the dominant chamber

A base `b` of a root pairing `P` is simultaneously a base `b.flip` of the flipped pairing `P.flip`,
so Mathlib's positivity predicate `RootPairing.Base.IsPos` measures both a root against the simple
roots and the corresponding coroot against the simple coroots. This file proves that the two
measurements agree, so that the coroot of a positive root is a nonnegative integer combination of
the simple coroots.

The dominant chamber is cut out by the signs of the *simple* coroot functionals. The agreement
above upgrades this to all of the positive roots at once: a weight is dominant exactly when every
positive coroot functional is nonnegative on it, and interior exactly when every positive coroot
functional is positive on it. A Weyl-group element matches the coroot functional of a root with
that of its image, so an element carrying an interior weight back into the closed dominant chamber
sends no positive root to a negative one.

## Main results

* `TauCeti.RootPairing.Base.isPos_flip_iff`: a root is positive for a base exactly when its coroot
  is positive for that base.
* `TauCeti.posRoots_flip`: a base and its flip have the same positive roots.
* `TauCeti.exists_coroot_eq_sum_nat_of_mem_posRoots`: the coroot of a positive root is a
  nonnegative integer combination of the simple coroots.
* `TauCeti.mem_dominantChamber_iff_forall_mem_posRoots` and
  `TauCeti.mem_openDominantChamber_iff_forall_mem_posRoots`: the dominant chamber and its interior
  are cut out by the positive coroot functionals, not just the simple ones.
* `TauCeti.RootPairing.coroot'_weylGroupToPerm_smul`: a Weyl-group element carries the coroot
  functional of a root to the coroot functional of its image.
* `TauCeti.inversions_eq_empty_of_smul_mem_dominantChamber`: an element carrying an interior weight
  into the closed dominant chamber has no inversions.

## Implementation notes

Mathlib deduces `P.flip.IsReduced` from `P.IsReduced` only in the presence of
`Module.IsTorsionFree R M` and `Module.IsTorsionFree R N`, both automatic over a field, so those
hypotheses are carried by every statement below that measures a coroot against the base.

## References

This file supplies the coroot-side positivity that the fundamental-domain item of Layer 4 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md` consumes, on top of the chamber
definitions already in `TauCeti/LinearAlgebra/RootSystem/Chamber.lean`. The argument is the one in
J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. III, §10.
-/

public section

open Function Set

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) [CharZero R] (b : P.Base)

namespace RootPairing.Base

/-- Root negation reverses positivity. This is Mathlib's `RootPairing.Base.IsPos.neg_iff_not`
phrased through `reflectionPerm`, which is the form the flipped pairing shares with `P`. -/
private lemma isPos_reflectionPerm_self_iff_not (k : ι) :
    b.IsPos (P.reflectionPerm k k) ↔ ¬ b.IsPos k :=
  (isPos_reflectionPerm_self_iff_mem_negRoots P b k).trans (mem_negRoots P b k)

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- A simple reflection preserves and reflects positivity of every root other than its own simple
root and the negative of that simple root. -/
lemma isPos_reflectionPerm_iff {i j : ι} (hj : j ∈ b.support) (hij : i ≠ j)
    (hij' : i ≠ P.reflectionPerm j j) :
    b.IsPos (P.reflectionPerm j i) ↔ b.IsPos i := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.reflectionPerm hj hij⟩
  have hne : P.reflectionPerm j i ≠ j := fun hc ↦ hij' (by rw [← P.reflectionPerm_self j i, hc])
  simpa [P.reflectionPerm_self] using h.reflectionPerm hj hne

variable [Module.IsTorsionFree R M] [Module.IsTorsionFree R N]

/-- **A root is positive for a base exactly when its coroot is positive for that base.** Both sides
are exchanged by root negation and preserved by the simple reflections, and both hold for the simple
roots, so the positive-root induction propagates the equivalence over the whole index type. -/
theorem isPos_flip_iff (i : ι) : b.flip.IsPos i ↔ b.IsPos i := by
  -- The flipped pairing reflects root indices by the very same permutations.
  have hflip : ∀ k l : ι, P.flip.reflectionPerm k l = P.reflectionPerm k l := fun _ _ ↦ rfl
  -- Both sides hold for a simple root.
  have hsimple : ∀ k ∈ b.support, (b.flip.IsPos k ↔ b.IsPos k) := fun k hk ↦ by
    simp only [b.isPos_of_mem_support hk, iff_true]
    exact b.flip.isPos_of_mem_support (by simpa using hk)
  -- Root negation reverses both sides at once.
  have hneg : ∀ k : ι, (b.flip.IsPos k ↔ b.IsPos k) →
      (b.flip.IsPos (P.reflectionPerm k k) ↔ b.IsPos (P.reflectionPerm k k)) := fun k hk ↦ by
    rw [isPos_reflectionPerm_self_iff_not P b k, ← hflip k k,
      isPos_reflectionPerm_self_iff_not P.flip b.flip k, hk]
  refine b.induction_reflect (p := fun k ↦ b.flip.IsPos k ↔ b.IsPos k) i hneg hsimple
    fun j k hj hk ↦ ?_
  rcases eq_or_ne j k with rfl | hjk
  · exact hneg j hj
  rcases eq_or_ne j (P.reflectionPerm k k) with rfl | hjk'
  · rw [P.reflectionPerm_self k k]
    exact hsimple k hk
  · rw [isPos_reflectionPerm_iff P b hk hjk hjk', ← hflip k j,
      isPos_reflectionPerm_iff P.flip b.flip (by simpa using hk) hjk (by rwa [hflip k k])]
    exact hj

end RootPairing.Base

section Coroot

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] [Module.IsTorsionFree R M]
  [Module.IsTorsionFree R N]

/-- A base and its flip have the same positive roots. -/
theorem posRoots_flip : posRoots P.flip b.flip = posRoots P b := by
  ext i
  simpa only [mem_posRoots] using RootPairing.Base.isPos_flip_iff P b i

/-- A base and its flip have the same negative roots. -/
theorem negRoots_flip : negRoots P.flip b.flip = negRoots P b := by
  ext i
  simpa only [mem_negRoots] using not_congr (RootPairing.Base.isPos_flip_iff P b i)

/-- The coroot of a positive root is a nonnegative integer combination of the simple coroots. -/
theorem exists_coroot_eq_sum_nat_of_mem_posRoots {i : ι} (hi : i ∈ posRoots P b) :
    ∃ f : ι → ℕ, f.support ⊆ b.support ∧
      P.coroot i = ∑ j ∈ b.support, f j • P.coroot j := by
  obtain ⟨f, hf, hsum⟩ := exists_root_eq_sum_nat_of_mem_posRoots P.flip b.flip
    (by rw [posRoots_flip]; exact hi)
  exact ⟨f, by simpa using hf, by simpa using hsum⟩

/-- A positive coroot functional is a nonnegative integer combination of the simple coroot
functionals, with at least one simple coroot genuinely occurring. -/
private lemma exists_coroot'_eq_sum_nat_of_mem_posRoots {i : ι} (hi : i ∈ posRoots P b) :
    ∃ f : ι → ℕ, (∃ j ∈ b.support, f j ≠ 0) ∧
      ∀ x : M, P.coroot' i x = ∑ j ∈ b.support, (f j : R) * P.coroot' j x := by
  obtain ⟨f, -, hsum⟩ := exists_coroot_eq_sum_nat_of_mem_posRoots P b hi
  refine ⟨f, ?_, fun x ↦ ?_⟩
  · by_contra hcon
    push Not at hcon
    haveI : NeZero (2 : R) := ⟨by exact_mod_cast (by norm_num : (2 : ℕ) ≠ 0)⟩
    refine P.ne_zero' i ?_
    rw [hsum]
    exact Finset.sum_eq_zero fun j hj ↦ by simp [hcon j hj]
  · have hcoroot' : P.coroot' i = ∑ j ∈ b.support, (f j : R) • P.coroot' j := by
      rw [show P.coroot' i = P.toLinearMap.flip (P.coroot i) from rfl, hsum, map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by
        simp [_root_.RootPairing.coroot', Nat.cast_smul_eq_nsmul]
    rw [hcoroot', LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ ↦ by simp

end Coroot

namespace RootPairing

omit [CharZero R] in
/-- An automorphism of a root pairing transports coroot functionals along its action on weights. -/
lemma coroot'_smul (g : P.Aut) (i : ι) (x : M) :
    P.coroot' i (g • x) = P.coroot' (g.indexEquiv.symm i) x := by
  have h := congrFun (congrArg DFunLike.coe
    (_root_.RootPairing.Hom.weight_coweight_transpose_apply P P (P.coroot i) g.toHom)) x
  simp only [LinearMap.dualMap_apply, _root_.RootPairing.Hom.coroot_coweightMap_apply] at h
  exact h

omit [CharZero R] in
/-- **A Weyl-group element matches the coroot functional of a root with the coroot functional of
its image.** -/
lemma coroot'_weylGroupToPerm_smul (w : P.weylGroup) (i : ι) (x : M) :
    P.coroot' (P.weylGroupToPerm w i) (w • x) = P.coroot' i x := by
  have h := coroot'_smul P (w : P.Aut) ((w : P.Aut).indexEquiv i) x
  rw [_root_.Equiv.symm_apply_apply] at h
  exact h

end RootPairing

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [Module.IsTorsionFree R M] [Module.IsTorsionFree R N] {x : M}

/-- Every positive coroot functional is nonnegative on the closed dominant chamber. -/
theorem coroot'_nonneg_of_mem_posRoots (hx : x ∈ dominantChamber P b) {i : ι}
    (hi : i ∈ posRoots P b) : 0 ≤ P.coroot' i x := by
  obtain ⟨f, -, hsum⟩ := exists_coroot'_eq_sum_nat_of_mem_posRoots P b hi
  rw [hsum x]
  exact Finset.sum_nonneg fun j hj ↦
    mul_nonneg (by positivity) ((mem_dominantChamber P b x).mp hx j hj)

/-- Every negative coroot functional is nonpositive on the closed dominant chamber. -/
theorem coroot'_nonpos_of_mem_negRoots (hx : x ∈ dominantChamber P b) {i : ι}
    (hi : i ∈ negRoots P b) : P.coroot' i x ≤ 0 := by
  have h := coroot'_nonneg_of_mem_posRoots P b hx
    ((reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b i).mpr hi)
  rw [RootPairing.coroot'_reflectionPerm_self] at h
  simpa using h

/-- Every positive coroot functional is positive on the open dominant chamber: some simple coroot
occurs in its expansion, because a coroot is never zero. -/
theorem coroot'_pos_of_mem_posRoots (hx : x ∈ openDominantChamber P b) {i : ι}
    (hi : i ∈ posRoots P b) : 0 < P.coroot' i x := by
  obtain ⟨f, ⟨j, hj, hfj⟩, hsum⟩ := exists_coroot'_eq_sum_nat_of_mem_posRoots P b hi
  have hx' := (mem_openDominantChamber P b x).mp hx
  rw [hsum x]
  refine Finset.sum_pos' (fun k hk ↦ mul_nonneg (by positivity) (hx' k hk).le) ⟨j, hj, ?_⟩
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hfj) (hx' j hj)

/-- Every negative coroot functional is negative on the open dominant chamber. -/
theorem coroot'_neg_of_mem_negRoots (hx : x ∈ openDominantChamber P b) {i : ι}
    (hi : i ∈ negRoots P b) : P.coroot' i x < 0 := by
  have h := coroot'_pos_of_mem_posRoots P b hx
    ((reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b i).mpr hi)
  rw [RootPairing.coroot'_reflectionPerm_self] at h
  simpa using h

/-- **The closed dominant chamber is cut out by the positive coroot functionals**, not just by the
simple ones. -/
theorem mem_dominantChamber_iff_forall_mem_posRoots :
    x ∈ dominantChamber P b ↔ ∀ i ∈ posRoots P b, 0 ≤ P.coroot' i x := by
  refine ⟨fun hx _ hi ↦ coroot'_nonneg_of_mem_posRoots P b hx hi, fun h ↦ ?_⟩
  exact (mem_dominantChamber P b x).mpr fun i hi ↦ h i (support_subset_posRoots P b hi)

/-- **The open dominant chamber is cut out by the positive coroot functionals**, not just by the
simple ones. -/
theorem mem_openDominantChamber_iff_forall_mem_posRoots :
    x ∈ openDominantChamber P b ↔ ∀ i ∈ posRoots P b, 0 < P.coroot' i x := by
  refine ⟨fun hx _ hi ↦ coroot'_pos_of_mem_posRoots P b hx hi, fun h ↦ ?_⟩
  exact (mem_openDominantChamber P b x).mpr fun i hi ↦ h i (support_subset_posRoots P b hi)

/-- A Weyl-group element carrying a weight interior to the dominant chamber back into the closed
dominant chamber keeps every positive root positive: the coroot functional of the image at the
moved weight is the coroot functional of the root at the original weight, hence positive. -/
theorem mapsTo_posRoots_of_smul_mem_dominantChamber (w : P.weylGroup)
    (hx : x ∈ openDominantChamber P b) (hw : w • x ∈ dominantChamber P b) :
    MapsTo (P.weylGroupToPerm w) (posRoots P b) (posRoots P b) := by
  intro i hi
  by_contra hneg
  rw [not_mem_posRoots_iff_mem_negRoots] at hneg
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

end Ordered

end TauCeti
