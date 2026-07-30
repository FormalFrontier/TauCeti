/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.WeylGroup

public section

/-!
# The dominant chamber of a base

Over a linearly ordered coefficient ring the simple coroots of a base cut the weight space into
sign-pattern cones, the Weyl chambers. This file introduces the dominant one, both closed and
open, and proves that it meets every Weyl orbit: every weight can be moved into the closed
dominant chamber by some element of the Weyl group. Equivalently, the Weyl translates of the
closed dominant chamber cover the whole weight space.

The proof is the classical maximization argument. The Weyl group of a finite root system is
finite, so the sum of the coroot functionals indexed by the positive roots, evaluated along an
orbit, attains a maximum. A simple reflection `sᵢ` permutes the positive roots other than `αᵢ`
and sends `αᵢ` to `-αᵢ`, so applying `sᵢ` changes that sum by `-2⟨αᵢ^∨, x⟩`; maximality
therefore forces `⟨αᵢ^∨, x⟩ ≥ 0` for every simple root, which is dominance.

## Main definitions

* `TauCeti.dominantChamber` is the closed dominant chamber of a base.
* `TauCeti.openDominantChamber` is its open counterpart.

## Main results

* `TauCeti.exists_mem_dominantChamber_of_finite_weylGroup` and
  `TauCeti.exists_mem_dominantChamber`: every weight is Weyl-conjugate into the closed dominant
  chamber.
* `TauCeti.iUnion_smul_dominantChamber_eq_univ`: the Weyl translates of the closed dominant
  chamber cover the weight space.
* `TauCeti.ofIdx_smul_notMem_dominantChamber` and
  `TauCeti.ofIdx_smul_ne_of_mem_openDominantChamber`: a simple reflection moves every point of the
  open dominant chamber, and moves it out of the closed chamber.

## Implementation notes

The roadmap states this layer over `ℝ`. Nothing in the argument uses completeness, division, or
the archimedean property, so the statements here are made over an arbitrary linearly ordered
commutative ring; `ℝ` and `ℚ` are the intended instances.

The maximization argument is proved as `exists_mem_dominantChamber_of_finite_weylGroup`, which
asks for no root-system assumption: on top of the standing `Finite ι`, `P.IsCrystallographic` and
`P.IsReduced` hypotheses that the positive-root permutation step needs, it assumes only
`Finite P.weylGroup`. The roadmap-signature `exists_mem_dominantChamber` is the root-system case,
where that finiteness comes from `TauCeti.RootPairing.finite_weylGroup`.

## References

This file implements the chamber definitions of Layer 4 ("Weyl chambers as cones") and the
existence half of its fundamental-domain item (`exists_mem_dominantChamber`) in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`, following the target signatures in
that roadmap's `Suggested.lean`. Uniqueness of the dominant representative is not proved here.

The argument is the one in J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, GTM 9, Ch. III, §10.3.
-/

namespace TauCeti

open Pointwise Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

variable [LinearOrder R] (b : P.Base)

/-- The closed dominant chamber of a base: the weights on which every simple coroot is
nonnegative. -/
def dominantChamber : Set M := {x | ∀ i ∈ b.support, 0 ≤ P.coroot' i x}

/-- The open dominant chamber of a base: the weights on which every simple coroot is positive. -/
def openDominantChamber : Set M := {x | ∀ i ∈ b.support, 0 < P.coroot' i x}

/-- Membership in the closed dominant chamber. -/
@[simp]
lemma mem_dominantChamber (x : M) :
    x ∈ dominantChamber P b ↔ ∀ i ∈ b.support, 0 ≤ P.coroot' i x := Iff.rfl

/-- Membership in the open dominant chamber. -/
@[simp]
lemma mem_openDominantChamber (x : M) :
    x ∈ openDominantChamber P b ↔ ∀ i ∈ b.support, 0 < P.coroot' i x := Iff.rfl

/-- The open dominant chamber is contained in the closed one. -/
lemma openDominantChamber_subset_dominantChamber :
    openDominantChamber P b ⊆ dominantChamber P b :=
  fun _ hx i hi ↦ (hx i hi).le

/-- The origin is dominant. -/
lemma zero_mem_dominantChamber : (0 : M) ∈ dominantChamber P b := by
  simp

variable [IsStrictOrderedRing R]

/-- The closed dominant chamber is closed under addition. -/
lemma add_mem_dominantChamber {x y : M} (hx : x ∈ dominantChamber P b)
    (hy : y ∈ dominantChamber P b) : x + y ∈ dominantChamber P b :=
  fun i hi ↦ by simpa using add_nonneg (hx i hi) (hy i hi)

/-- The closed dominant chamber is closed under nonnegative scaling. -/
lemma smul_mem_dominantChamber {t : R} (ht : 0 ≤ t) {x : M} (hx : x ∈ dominantChamber P b) :
    t • x ∈ dominantChamber P b :=
  fun i hi ↦ by simpa using mul_nonneg ht (hx i hi)

/-- The open dominant chamber is closed under addition. -/
lemma add_mem_openDominantChamber {x y : M} (hx : x ∈ openDominantChamber P b)
    (hy : y ∈ openDominantChamber P b) : x + y ∈ openDominantChamber P b :=
  fun i hi ↦ by simpa using add_pos (hx i hi) (hy i hi)

/-- The open dominant chamber is closed under positive scaling. -/
lemma smul_mem_openDominantChamber {t : R} (ht : 0 < t) {x : M}
    (hx : x ∈ openDominantChamber P b) : t • x ∈ openDominantChamber P b :=
  fun i hi ↦ by simpa using mul_pos ht (hx i hi)

/-- A simple reflection carries every point of the open dominant chamber out of the closed
dominant chamber, since it reverses the sign of the corresponding simple coroot. -/
theorem ofIdx_smul_notMem_dominantChamber {i : ι} (hi : i ∈ b.support) {x : M}
    (hx : x ∈ openDominantChamber P b) :
    RootPairing.weylGroup.ofIdx P i • x ∉ dominantChamber P b := by
  intro hmem
  have h := hmem i hi
  rw [_root_.RootPairing.weylGroup.ofIdx_smul, _root_.RootPairing.Equiv.reflection_smul,
    RootPairing.coroot'_reflection_self] at h
  have := hx i hi
  linarith

/-- No simple reflection fixes a point of the open dominant chamber: it would otherwise stay in
the closed dominant chamber. -/
theorem ofIdx_smul_ne_of_mem_openDominantChamber {i : ι} (hi : i ∈ b.support) {x : M}
    (hx : x ∈ openDominantChamber P b) :
    RootPairing.weylGroup.ofIdx P i • x ≠ x := by
  intro hfix
  refine ofIdx_smul_notMem_dominantChamber P b hi hx ?_
  rw [hfix]
  exact openDominantChamber_subset_dominantChamber P b hx

section Finite

variable [Finite ι]

/-- The sum of the coroot functionals indexed by the positive roots, evaluated at `x`. Up to the
factor two this is the pairing of `x` with the Weyl vector on the coroot side; all that is used
below is how it transforms under a simple reflection. -/
private noncomputable def posCorootSum (x : M) : R :=
  ∑ i ∈ (posRoots_finite P b).toFinset, P.coroot' i x

variable [P.IsCrystallographic] [P.IsReduced]

/-- A simple reflection changes `posCorootSum` by twice the value of its own simple coroot. The
reflection permutes the positive roots other than its own simple root, and negates that one. -/
private lemma posCorootSum_reflection {i : ι} (hi : i ∈ b.support) (x : M) :
    posCorootSum P b (P.reflection i x) = posCorootSum P b x - 2 * P.coroot' i x := by
  classical
  -- Work with the underlying sums rather than leaning on `posCorootSum` unfolding silently.
  unfold posCorootSum
  set s := (posRoots_finite P b).toFinset with hs
  have hmem : ∀ j : ι, j ∈ s ↔ j ∈ posRoots P b := by
    intro j; rw [hs, Set.Finite.mem_toFinset]
  have his : i ∈ s := (hmem i).mpr (support_subset_posRoots P b hi)
  -- Reflecting the argument reindexes the summand along `P.reflectionPerm i`.
  have hreindex : ∑ j ∈ s, P.coroot' j (P.reflection i x) =
      ∑ j ∈ s, P.coroot' (P.reflectionPerm i j) x :=
    Finset.sum_congr rfl fun _ _ ↦ P.coroot'_reflection x
  -- The reflected simple coroot is the negative of the original.
  have hself : P.coroot' (P.reflectionPerm i i) x = -P.coroot' i x := by
    rw [RootPairing.coroot'_reflectionPerm_self]
    simp
  -- Away from `i` the reflection is a bijection of the punctured positive roots.
  have hpunctured : ∑ j ∈ s.erase i, P.coroot' (P.reflectionPerm i j) x =
      ∑ j ∈ s.erase i, P.coroot' j x := by
    refine Finset.sum_equiv (P.reflectionPerm i) (fun j ↦ ?_) (fun _ _ ↦ rfl)
    have h := reflectionPerm_mem_posRoots_diff_singleton_iff P b hi j
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at h
    simp only [Finset.mem_erase, hmem]
    tauto
  have hexpand : ∑ j ∈ s, P.coroot' j x = P.coroot' i x + ∑ j ∈ s.erase i, P.coroot' j x :=
    (Finset.add_sum_erase _ _ his).symm
  rw [hreindex, ← Finset.add_sum_erase _ _ his, hpunctured, hself, hexpand]
  ring

section FiniteWeylGroup

variable [Finite P.weylGroup]

/-- **Every weight is Weyl-conjugate into the closed dominant chamber**, for a crystallographic
reduced pairing with finitely many roots whose Weyl group is finite. Maximizing `posCorootSum`
along the orbit produces the dominant representative. -/
theorem exists_mem_dominantChamber_of_finite_weylGroup (x : M) :
    ∃ w : P.weylGroup, w • x ∈ dominantChamber P b := by
  obtain ⟨w, hw⟩ := Finite.exists_max fun w : P.weylGroup ↦ posCorootSum P b (w • x)
  refine ⟨w, fun i hi ↦ ?_⟩
  have hsmul : (RootPairing.weylGroup.ofIdx P i * w) • x = P.reflection i (w • x) := by
    simp [mul_smul]
  have hle := hw (RootPairing.weylGroup.ofIdx P i * w)
  rw [hsmul, posCorootSum_reflection P b hi] at hle
  linarith

/-- Every Weyl orbit meets the closed dominant chamber. -/
theorem orbit_inter_dominantChamber_nonempty (x : M) :
    (MulAction.orbit P.weylGroup x ∩ dominantChamber P b).Nonempty := by
  obtain ⟨w, hw⟩ := exists_mem_dominantChamber_of_finite_weylGroup P b x
  exact ⟨w • x, ⟨w, rfl⟩, hw⟩

/-- **The Weyl translates of the closed dominant chamber cover the weight space.** -/
theorem iUnion_smul_dominantChamber_eq_univ :
    ⋃ w : P.weylGroup, w • dominantChamber P b = (univ : Set M) := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨w, hw⟩ := exists_mem_dominantChamber_of_finite_weylGroup P b x
  refine Set.mem_iUnion.mpr ⟨w⁻¹, ?_⟩
  exact ⟨w • x, hw, inv_smul_smul w x⟩

end FiniteWeylGroup

/-- **Every weight is Weyl-conjugate into the closed dominant chamber.** Together with the
uniqueness of that representative this says the closed dominant chamber is a fundamental domain
for the Weyl group. -/
theorem exists_mem_dominantChamber [P.IsRootSystem] (x : M) :
    ∃ w : P.weylGroup, w • x ∈ dominantChamber P b :=
  letI := RootPairing.finite_weylGroup P
  exists_mem_dominantChamber_of_finite_weylGroup P b x

end Finite

end TauCeti
