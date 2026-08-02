/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Deletion

public section

/-!
# The longest element of a finite Weyl group

A finite Weyl group contains exactly one element sending every positive root to a negative root:
the longest element `w₀`. This file constructs it, proves it unique, and records its three
defining properties, namely that its inversion set is all of the positive roots, that it maximizes
the number of inversions, and that it is an involution.

The construction is the maximization argument. The Weyl group is finite, so some `w` has as many
inversions as possible. If a simple root `αᵢ` were not an inversion of `w`, then `w sᵢ` would have
one inversion more, so every simple root is an inversion of `w`; and a Weyl-group element sending
every simple root to a negative root sends every positive root to a negative root, because a
positive root is a sum of simple roots and heights add. Uniqueness is the observation that if `v`
and `w` both reverse all the signs then `v⁻¹ w` preserves them, so it has no inversions and is the
identity.

Since the number of inversions of a Weyl-group element is its Coxeter length, the statements below
are the usual ones about `w₀`: it is the unique element of maximal length, that length is the
number of positive roots, and `w₀² = 1`. The Coxeter presentation of the Weyl group is not
available here, so length is spelled throughout as `(inversions P b w).ncard`.

## Main definitions

* `TauCeti.longestElement` is the longest element `w₀` of the Weyl group of a finite root system.

## Main results

* `TauCeti.exists_inversions_eq_posRoots_of_finite_weylGroup` and
  `TauCeti.eq_of_inversions_eq_posRoots`: exactly one Weyl-group element inverts every positive
  root.
* `TauCeti.inversions_longestElement` and `TauCeti.image_posRoots_longestElement`: `w₀` exchanges
  the positive and the negative roots.
* `TauCeti.ncard_inversions_le_ncard_inversions_longestElement` and
  `TauCeti.eq_longestElement_iff_ncard_inversions`: `w₀` is the unique element of maximal length,
  and that length is the number of positive roots.
* `TauCeti.longestElement_inv` and `TauCeti.longestElement_sq`: `w₀` is an involution.
* `TauCeti.smul_dominantChamber_longestElement`: `w₀` carries the dominant chamber onto its
  negative, the antidominant chamber.

## Implementation notes

`TauCeti.longestElement` is defined for a root system, where
`TauCeti.RootPairing.finite_weylGroup` supplies the finiteness of the Weyl group. The existence
theorem behind it is proved one level more generally, for a crystallographic reduced pairing with
finitely many roots whose Weyl group happens to be finite; that is the shape used in
`TauCeti/LinearAlgebra/RootSystem/Chamber.lean` as well.

## References

This file implements the "longest element" item of Layer 4 in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The roadmap's `Suggested.lean` states
the length clause with the Coxeter length of the Weyl Coxeter system, which is the Layer 2 summit
and is not yet available; the inversion count that replaces it here is what that layer's "length
equals inversions" item identifies with Coxeter length. The argument is the one in J. E. Humphreys,
*Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. III, §10.3.
-/

namespace TauCeti

open Function Pointwise Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

section Combinatorics

variable [CharZero R] (b : P.Base)

variable {P b} in
/-- An element inverting every positive root sends every negative root to a positive root, since
root negation intertwines the two halves. -/
theorem mapsTo_negRoots_posRoots_of_inversions_eq_posRoots {w : P.weylGroup}
    (h : inversions P b w = posRoots P b) :
    MapsTo (P.weylGroupToPerm w) (negRoots P b) (posRoots P b) := by
  letI := P.indexNeg
  intro i hi
  have hpos : -i ∈ posRoots P b := by
    rwa [mem_posRoots, RootPairing.Base.IsPos.neg_iff_not, ← mem_negRoots]
  have himage := (inversions_eq_posRoots_iff P b w).mp h hpos
  rw [RootPairing.weylGroupToPerm_neg, mem_negRoots, RootPairing.Base.IsPos.neg_iff_not,
    not_not] at himage
  exact (mem_posRoots P b _).mpr himage

variable {P b} in
/-- The inverse of an element inverting every positive root inverts every positive root. -/
theorem inversions_inv_eq_posRoots {w : P.weylGroup} (h : inversions P b w = posRoots P b) :
    inversions P b w⁻¹ = posRoots P b := by
  rw [inversions_eq_posRoots_iff] at h ⊢
  intro i hi
  rw [← not_mem_posRoots_iff_mem_negRoots]
  intro hpos
  -- Were the image positive, applying `w` to it would put `i` back among the negative roots.
  have hback : P.weylGroupToPerm w (P.weylGroupToPerm w⁻¹ i) = i := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have himage := h hpos
  rw [hback, ← not_mem_posRoots_iff_mem_negRoots] at himage
  exact himage hi

variable [Finite ι] [IsDomain R] [P.IsCrystallographic]

variable {P b} in
/-- **A Weyl-group element sending every simple root to a negative root sends every positive root
to a negative root.** A positive root is built up from simple roots by addition, and the height of
a sum of two roots is the sum of their heights, so the image again has negative height. -/
theorem mapsTo_posRoots_negRoots_of_forall_mem_support {w : P.weylGroup}
    (h : ∀ i ∈ b.support, P.weylGroupToPerm w i ∈ negRoots P b) :
    MapsTo (P.weylGroupToPerm w) (posRoots P b) (negRoots P b) := by
  -- Negativity of the image is negativity of its height, which is what the induction adds up.
  have hneg : ∀ j : ι, P.weylGroupToPerm w j ∈ negRoots P b ↔
      b.height (P.weylGroupToPerm w j) < 0 := fun j ↦ by
    rw [mem_negRoots, RootPairing.Base.isPos_iff']
    exact not_le
  intro i hi
  refine (hneg i).mpr ?_
  refine RootPairing.Base.IsPos.induction_on_add ((mem_posRoots P b i).mp hi)
    (p := fun j ↦ b.height (P.weylGroupToPerm w j) < 0) (fun j hj ↦ (hneg j).mp (h j hj))
    fun j k l hl hj hk ↦ ?_
  -- The Weyl-group element carries the decomposition `root l = root j + root k` to the images.
  have himage : P.root (P.weylGroupToPerm w l) =
      P.root (P.weylGroupToPerm w j) + P.root (P.weylGroupToPerm w k) := by
    rw [← P.weylGroup_apply_root w l, ← P.weylGroup_apply_root w j, ← P.weylGroup_apply_root w k,
      hl, smul_add]
  have hk' := (hneg k).mp (h k hk)
  rw [b.height_add himage]
  omega

variable {P b} in
/-- A Weyl-group element every simple root of which is an inversion inverts every positive
root. -/
theorem inversions_eq_posRoots_of_support_subset {w : P.weylGroup}
    (h : ↑b.support ⊆ inversions P b w) : inversions P b w = posRoots P b :=
  (inversions_eq_posRoots_iff P b w).mpr <| mapsTo_posRoots_negRoots_of_forall_mem_support
    fun i hi ↦ (mem_negRoots P b _).mpr ((mem_inversions P b w i).mp (h hi)).2

variable [P.IsReduced]

variable {P b} in
/-- **At most one Weyl-group element inverts every positive root.** If `v` and `w` both do, then
`v⁻¹ w` keeps every positive root positive, hence is the identity. -/
theorem eq_of_inversions_eq_posRoots {v w : P.weylGroup} (hv : inversions P b v = posRoots P b)
    (hw : inversions P b w = posRoots P b) : v = w := by
  have hmaps : MapsTo (P.weylGroupToPerm (v⁻¹ * w)) (posRoots P b) (posRoots P b) := by
    intro i hi
    rw [map_mul, Equiv.Perm.mul_apply]
    exact mapsTo_negRoots_posRoots_of_inversions_eq_posRoots (inversions_inv_eq_posRoots hv)
      ((inversions_eq_posRoots_iff P b w).mp hw hi)
  exact inv_mul_eq_one.mp (eq_one_of_mapsTo_posRoots (b := b) hmaps)

section FiniteWeylGroup

variable [Finite P.weylGroup]

/-- **Some Weyl-group element inverts every positive root**, for a crystallographic reduced pairing
with finitely many roots whose Weyl group is finite. An element with as many inversions as possible
has every simple root among its inversions, since otherwise appending that simple reflection would
produce one inversion more. -/
theorem exists_inversions_eq_posRoots_of_finite_weylGroup :
    ∃ w : P.weylGroup, inversions P b w = posRoots P b := by
  obtain ⟨w, hw⟩ := Finite.exists_max fun w : P.weylGroup ↦ (inversions P b w).ncard
  refine ⟨w, inversions_eq_posRoots_of_support_subset fun i hi ↦ ?_⟩
  by_contra hiw
  have hgrow := ncard_inversions_mul_ofIdx_of_notMem P w b hi hiw
  have hle := hw (w * RootPairing.weylGroup.ofIdx P i)
  omega

end FiniteWeylGroup

variable [P.IsRootSystem]

/-- **The longest element `w₀` of a finite Weyl group**: the unique element sending every positive
root to a negative root. Its inversion set is all of the positive roots, so among all Weyl-group
elements it has the most inversions, that is, the greatest Coxeter length. -/
noncomputable def longestElement : P.weylGroup :=
  letI := RootPairing.finite_weylGroup P
  (exists_inversions_eq_posRoots_of_finite_weylGroup P b).choose

/-- **The longest element inverts every positive root.** -/
@[simp]
theorem inversions_longestElement : inversions P b (longestElement P b) = posRoots P b :=
  letI := RootPairing.finite_weylGroup P
  (exists_inversions_eq_posRoots_of_finite_weylGroup P b).choose_spec

/-- **The longest element sends every positive root to a negative root.** -/
theorem mapsTo_posRoots_negRoots_longestElement :
    MapsTo (P.weylGroupToPerm (longestElement P b)) (posRoots P b) (negRoots P b) :=
  (inversions_eq_posRoots_iff P b _).mp (inversions_longestElement P b)

/-- The longest element sends every negative root to a positive root. -/
theorem mapsTo_negRoots_posRoots_longestElement :
    MapsTo (P.weylGroupToPerm (longestElement P b)) (negRoots P b) (posRoots P b) :=
  mapsTo_negRoots_posRoots_of_inversions_eq_posRoots (inversions_longestElement P b)

variable {P b} in
/-- **The longest element is the only Weyl-group element inverting every positive root.** -/
theorem eq_longestElement_of_inversions_eq_posRoots {w : P.weylGroup}
    (h : inversions P b w = posRoots P b) : w = longestElement P b :=
  eq_of_inversions_eq_posRoots h (inversions_longestElement P b)

variable {P b} in
/-- A Weyl-group element is the longest element exactly when it inverts every positive root. -/
theorem eq_longestElement_iff {w : P.weylGroup} :
    w = longestElement P b ↔ inversions P b w = posRoots P b :=
  ⟨fun h ↦ h ▸ inversions_longestElement P b, eq_longestElement_of_inversions_eq_posRoots⟩

/-- **The longest element is its own inverse.** The inverse also inverts every positive root, and
only one element does. -/
@[simp]
theorem longestElement_inv : (longestElement P b)⁻¹ = longestElement P b :=
  eq_longestElement_of_inversions_eq_posRoots
    (inversions_inv_eq_posRoots (inversions_longestElement P b))

/-- **The longest element squares to the identity.** -/
@[simp]
theorem longestElement_sq : longestElement P b ^ 2 = 1 := by
  rw [sq]
  nth_rewrite 2 [← longestElement_inv P b]
  exact mul_inv_cancel _

/-- The longest element acts on the weight space as an involution. -/
theorem smul_smul_longestElement (x : M) :
    longestElement P b • longestElement P b • x = x := by
  rw [smul_smul, ← sq, longestElement_sq, one_smul]

/-- The permutation of the root indices induced by the longest element is an involution. -/
theorem weylGroupToPerm_longestElement_involutive :
    Involutive (P.weylGroupToPerm (longestElement P b)) := fun i ↦ by
  rw [← Equiv.Perm.mul_apply, ← map_mul, ← sq, longestElement_sq, map_one]
  rfl

/-- **The longest element exchanges the positive and the negative roots.** -/
theorem image_posRoots_longestElement :
    P.weylGroupToPerm (longestElement P b) '' posRoots P b = negRoots P b :=
  Subset.antisymm (image_subset_iff.mpr (mapsTo_posRoots_negRoots_longestElement P b))
    fun i hi ↦ ⟨_, mapsTo_negRoots_posRoots_longestElement P b hi,
      weylGroupToPerm_longestElement_involutive P b i⟩

/-- **The longest element exchanges the negative and the positive roots.** -/
theorem image_negRoots_longestElement :
    P.weylGroupToPerm (longestElement P b) '' negRoots P b = posRoots P b :=
  Subset.antisymm (image_subset_iff.mpr (mapsTo_negRoots_posRoots_longestElement P b))
    fun i hi ↦ ⟨_, mapsTo_posRoots_negRoots_longestElement P b hi,
      weylGroupToPerm_longestElement_involutive P b i⟩

/-- **The length of the longest element is the number of positive roots.** -/
theorem ncard_inversions_longestElement :
    (inversions P b (longestElement P b)).ncard = (posRoots P b).ncard := by
  rw [inversions_longestElement]

/-- **No Weyl-group element is longer than the longest element.** -/
theorem ncard_inversions_le_ncard_inversions_longestElement (w : P.weylGroup) :
    (inversions P b w).ncard ≤ (inversions P b (longestElement P b)).ncard := by
  rw [ncard_inversions_longestElement]
  exact ncard_inversions_le P b w

variable {P b} in
/-- **The longest element is the unique element of maximal length.** An element with as many
inversions as there are positive roots has all of them as inversions. -/
theorem eq_longestElement_iff_ncard_inversions {w : P.weylGroup} :
    w = longestElement P b ↔ (inversions P b w).ncard = (posRoots P b).ncard := by
  refine ⟨fun h ↦ h ▸ ncard_inversions_longestElement P b, fun h ↦ ?_⟩
  exact eq_longestElement_of_inversions_eq_posRoots
    (Set.eq_of_subset_of_ncard_le (inversions_subset_posRoots P b w) h.ge (posRoots_finite P b))

/-- A root system with at least one root has a longest element other than the identity. -/
theorem longestElement_ne_one [Nonempty ι] : longestElement P b ≠ 1 := by
  intro h
  have hpos := posRoots_nonempty P b
  rw [← inversions_longestElement P b, h, inversions_one] at hpos
  exact hpos.ne_empty rfl

/-- The longest element matches the simple coroot functionals at a weight with the coroot
functionals of the reversed roots at the moved weight. -/
theorem coroot'_smul_longestElement (i : ι) (x : M) :
    P.coroot' i (longestElement P b • x) =
      P.coroot' (P.weylGroupToPerm (longestElement P b) i) x := by
  conv_lhs => rw [← weylGroupToPerm_longestElement_involutive P b i]
  exact RootPairing.coroot'_weylGroupToPerm_smul P _ _ x

end Combinatorics

section Chamber

variable [LinearOrder R] [IsStrictOrderedRing R] (b : P.Base)
  [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced] [P.IsRootSystem]

variable {P b} in
/-- **The longest element carries the dominant chamber into its negative.** A simple coroot
functional evaluated on `w₀ • x` is the coroot functional of a negative root evaluated on `x`,
which is nonpositive when `x` is dominant. -/
theorem neg_smul_mem_dominantChamber_longestElement {x : M} (hx : x ∈ dominantChamber P b) :
    -(longestElement P b • x) ∈ dominantChamber P b := by
  rw [mem_dominantChamber]
  intro i hi
  have hneg := mapsTo_posRoots_negRoots_longestElement P b (support_subset_posRoots P b hi)
  rw [map_neg, coroot'_smul_longestElement P b i x]
  simpa using coroot'_nonpos_of_mem_negRoots P b hx hneg

variable {P b} in
/-- The longest element carries the interior of the dominant chamber into its negative. -/
theorem neg_smul_mem_openDominantChamber_longestElement {x : M}
    (hx : x ∈ openDominantChamber P b) :
    -(longestElement P b • x) ∈ openDominantChamber P b := by
  rw [mem_openDominantChamber]
  intro i hi
  have hneg := mapsTo_posRoots_negRoots_longestElement P b (support_subset_posRoots P b hi)
  rw [map_neg, coroot'_smul_longestElement P b i x]
  simpa using coroot'_neg_of_mem_negRoots P b hx hneg

/-- **The longest element carries the dominant chamber onto its negative**, the antidominant
chamber. This is the weight-space form of the statement that `w₀` reverses the sign of every
root. -/
theorem smul_dominantChamber_longestElement :
    longestElement P b • dominantChamber P b = -dominantChamber P b := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, longestElement_inv, Set.mem_neg]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [smul_smul_longestElement] using neg_smul_mem_dominantChamber_longestElement h
  · simpa [smul_neg] using neg_smul_mem_dominantChamber_longestElement h

end Chamber

end TauCeti
