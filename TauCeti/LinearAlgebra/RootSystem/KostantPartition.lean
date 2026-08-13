/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Positive
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import TauCeti.LinearAlgebra.RootSystem.Height

/-!
# The Kostant partition function

The Kostant partition function `P(ν)` counts the ways of writing an element `ν` of the ambient root
module as a sum of positive roots with multiplicity. This file defines it for a base of an arbitrary
root pairing, together with the finiteness statement that makes the count meaningful.

The multiplicities are recorded as a function `c : ι → ℕ` on root indices, supported on the
positive roots, and `TauCeti.IsKostantPartition P b ν c` says that `∑ᵢ cᵢ αᵢ = ν`. There are
not necessarily finitely many functions `ι → ℕ` when the index type is finite, so finiteness must be
proved before `Nat.card` represents the intended finite cardinality. The theorem
`TauCeti.finite_setOf_isKostantPartition` supplies this proof.

The bound comes from a fact about heights proved in
`TauCeti/LinearAlgebra/RootSystem/Height.lean`, since it has nothing to do with positivity:
`TauCeti.sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero` says that height respects
every integral relation among roots, so the total height `∑ᵢ cᵢ ht(αᵢ)` depends only on `ν` and not
on the partition. Fixing one partition of `ν`, its total height therefore bounds the total
multiplicity, and hence each multiplicity, of every other partition of `ν`.

## Main definitions

* `TauCeti.IsKostantPartition`: the predicate that a multiplicity function writes `ν` as a sum of
  positive roots.
* `TauCeti.kostantPartition`: the Kostant partition function, the number of such multiplicity
  functions.

## Main results

* `TauCeti.sum_natCast_mul_height_eq_of_isKostantPartition`: two Kostant partitions of the same
  element have the same total height.
* `TauCeti.finite_setOf_isKostantPartition`: an element has only finitely many Kostant partitions.
* `TauCeti.kostantPartition_zero`: `P(0) = 1`, the empty partition being the only one.
* `TauCeti.kostantPartition_root_of_mem_support`: `P(αᵢ) = 1` for a simple root `αᵢ`, which is the
  statement that a simple root is a sum of positive roots in only the obvious way.

## Roadmap

This is the “Kostant partition function” item of Layer 3 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, which asks for it “**here** in
Layer 3 as a combinatorial object attached to the positive roots”, to be consumed by the weight
multiplicities of a Verma module in that layer and by Kostant's multiplicity formula in Layer 6.
The target signature in that roadmap's `Suggested.lean` is `kostantPartition base nu` for a base of
the root system of a Killing-semisimple Lie algebra; nothing in the definition uses the Lie algebra,
so it is stated here for a base of an arbitrary root pairing, alongside
`TauCeti.posRoots` in `TauCeti/LinearAlgebra/RootSystem/Positive.lean`, and specializes to that
signature.

## References

* B. Kostant, *A formula for the multiplicity of a weight*, Trans. Amer. Math. Soc. **93** (1959).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §24.2.
-/

public section

namespace TauCeti

open Function Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [CharZero R]
  (P : RootPairing ι R M N) (b : P.Base)

/-! ## Kostant partitions -/

variable [Finite ι]

/-- **A Kostant partition of `ν`**: a multiplicity function `c` on root indices, supported on the
positive roots, whose weighted sum of positive roots is `ν`. -/
def IsKostantPartition (ν : M) (c : ι → ℕ) : Prop :=
  support c ⊆ posRoots P b ∧ ∑ i ∈ posRootsFinset P b, c i • P.root i = ν

/-- A multiplicity function is a Kostant partition exactly when it is supported on the positive
roots and its weighted root sum is the element being partitioned.

This is deliberately not a `simp` lemma: unfolding the predicate on sight would put every other
statement about it — `isKostantPartition_zero_iff` first of all — out of simp normal form. -/
theorem isKostantPartition_iff (ν : M) (c : ι → ℕ) :
    IsKostantPartition P b ν c ↔
      support c ⊆ posRoots P b ∧ ∑ i ∈ posRootsFinset P b, c i • P.root i = ν :=
  Iff.rfl

variable {P b}

/-- The defining sum of a Kostant partition, with the multiplicities read as integers. -/
theorem sum_zsmul_root_of_isKostantPartition {ν : M} {c : ι → ℕ}
    (hc : IsKostantPartition P b ν c) :
    ∑ i ∈ posRootsFinset P b, (c i : ℤ) • P.root i = ν := by
  simp_rw [natCast_zsmul]
  exact hc.2

/-- **The total height of a Kostant partition depends only on the element partitioned.** This is
what bounds the multiplicities, and hence what makes the partitions finite in number. -/
theorem sum_natCast_mul_height_eq_of_isKostantPartition {ν : M} {c c' : ι → ℕ}
    (hc : IsKostantPartition P b ν c) (hc' : IsKostantPartition P b ν c') :
    ∑ i ∈ posRootsFinset P b, (c i : ℤ) * b.height i
      = ∑ i ∈ posRootsFinset P b, (c' i : ℤ) * b.height i :=
  sum_mul_height_eq_of_sum_zsmul_root_eq P b
    ((sum_zsmul_root_of_isKostantPartition hc).trans
      (sum_zsmul_root_of_isKostantPartition hc').symm)

variable (P b)

private lemma natCast_mul_height_nonneg (c : ι → ℕ) (i : ι) (hi : i ∈ posRootsFinset P b) :
    0 ≤ (c i : ℤ) * b.height i := by
  have h := one_le_height_of_mem_posRoots P b ((mem_posRootsFinset P b i).mp hi)
  exact mul_nonneg (Int.natCast_nonneg _) (by omega)

private lemma natCast_le_sum_natCast_mul_height (c : ι → ℕ) {i : ι}
    (hi : i ∈ posRootsFinset P b) :
    (c i : ℤ) ≤ ∑ k ∈ posRootsFinset P b, (c k : ℤ) * b.height k := by
  refine le_trans ?_ (Finset.single_le_sum (natCast_mul_height_nonneg P b c) hi)
  exact le_mul_of_one_le_right (Int.natCast_nonneg _)
    (one_le_height_of_mem_posRoots P b ((mem_posRootsFinset P b i).mp hi))

/-- An element has only finitely many Kostant partitions. -/
theorem finite_setOf_isKostantPartition (ν : M) :
    {c : ι → ℕ | IsKostantPartition P b ν c}.Finite := by
  by_cases hne : ∃ c₀, IsKostantPartition P b ν c₀
  · obtain ⟨c₀, hc₀⟩ := hne
    -- The total height of `c₀` bounds every coordinate of every other partition.
    refine Set.Finite.subset (Set.Finite.pi fun _ : ι ↦ Set.finite_Iic
      (∑ k ∈ posRootsFinset P b, (c₀ k : ℤ) * b.height k).toNat) ?_
    intro c hc i _
    simp only [Set.mem_Iic]
    by_cases hi : i ∈ posRootsFinset P b
    · have h1 := natCast_le_sum_natCast_mul_height P b c hi
      rw [sum_natCast_mul_height_eq_of_isKostantPartition hc hc₀] at h1
      omega
    · have h0 : c i = 0 := by
        by_contra h
        exact hi ((mem_posRootsFinset P b i).mpr (hc.1 (mem_support.mpr h)))
      omega
  · have hempty : {c : ι → ℕ | IsKostantPartition P b ν c} = ∅ := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hc ↦ hne ⟨c, hc⟩
    rw [hempty]
    exact Set.finite_empty

/-- The Kostant partitions of an element form a finite type, so their `Nat.card` is their finite
cardinality. -/
instance instFiniteSubtypeIsKostantPartition (ν : M) :
    Finite {c : ι → ℕ // IsKostantPartition P b ν c} :=
  (finite_setOf_isKostantPartition P b ν).to_subtype

/-- **The Kostant partition function** `P(ν)`: the number of ways of writing `ν` as a sum of
positive roots with multiplicity. -/
noncomputable def kostantPartition (ν : M) : ℕ :=
  Nat.card {c : ι → ℕ // IsKostantPartition P b ν c}

/-- The Kostant partition function counts the Kostant partitions of its argument. -/
theorem kostantPartition_def (ν : M) :
    kostantPartition P b ν = Nat.card {c : ι → ℕ // IsKostantPartition P b ν c} := by
  rw [kostantPartition]

/-- The Kostant partition function is positive exactly on the elements that are a sum of positive
roots. -/
@[simp] theorem kostantPartition_pos_iff (ν : M) :
    0 < kostantPartition P b ν ↔ ∃ c, IsKostantPartition P b ν c := by
  rw [kostantPartition_def, Finite.card_pos_iff, nonempty_subtype]

/-- The Kostant partition function vanishes exactly off the set of sums of positive roots. -/
@[simp] theorem kostantPartition_eq_zero_iff (ν : M) :
    kostantPartition P b ν = 0 ↔ ¬ ∃ c, IsKostantPartition P b ν c := by
  rw [← kostantPartition_pos_iff, Nat.pos_iff_ne_zero, not_ne_iff]

/-! ## The two smallest values -/

/-- The zero multiplicity function is the unique Kostant partition of zero. -/
@[simp] theorem isKostantPartition_zero_iff {c : ι → ℕ} :
    IsKostantPartition P b (0 : M) c ↔ c = 0 := by
  refine ⟨fun hc ↦ ?_, ?_⟩
  -- A nonzero multiplicity would contribute positively to the total height.
  · have h0 : ∑ i ∈ posRootsFinset P b, (c i : ℤ) * b.height i = 0 :=
      sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero P b
        (sum_zsmul_root_of_isKostantPartition hc)
    have hterm : ∀ i ∈ posRootsFinset P b, (c i : ℤ) * b.height i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (natCast_mul_height_nonneg P b c)).mp h0
    funext i
    simp only [Pi.zero_apply]
    by_cases hi : i ∈ posRootsFinset P b
    · have h1 := one_le_height_of_mem_posRoots P b ((mem_posRootsFinset P b i).mp hi)
      have hci : (c i : ℤ) = 0 := by
        rcases mul_eq_zero.mp (hterm i hi) with h | h
        · exact h
        · omega
      exact_mod_cast hci
    · by_contra h
      exact hi ((mem_posRootsFinset P b i).mpr (hc.1 (mem_support.mpr h)))
  · rintro rfl
    exact ⟨by simp, by simp⟩

/-- `P(0) = 1`. -/
@[simp] theorem kostantPartition_zero : kostantPartition P b (0 : M) = 1 := by
  rw [kostantPartition_def, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y ↦ Subtype.ext ?_⟩, ⟨⟨0, (isKostantPartition_zero_iff P b).mpr rfl⟩⟩⟩
  exact ((isKostantPartition_zero_iff P b).mp x.2).trans
    ((isKostantPartition_zero_iff P b).mp y.2).symm

/-- A positive root is a sum of positive roots, namely of itself. -/
theorem isKostantPartition_single [DecidableEq ι] {i : ι} (hi : i ∈ posRoots P b) :
    IsKostantPartition P b (P.root i) (Pi.single i 1) := by
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · rw [mem_support] at hk
    by_cases hki : k = i
    · exact hki ▸ hi
    · simp [Pi.single_eq_of_ne hki] at hk
  · rw [Finset.sum_eq_single_of_mem i ((mem_posRootsFinset P b i).mpr hi)
      fun k _ hk ↦ by simp [Pi.single_eq_of_ne hk]]
    simp

/-- The Kostant partition function is positive on every positive root. -/
theorem kostantPartition_root_pos {i : ι} (hi : i ∈ posRoots P b) :
    0 < kostantPartition P b (P.root i) := by
  classical
  exact (kostantPartition_pos_iff P b _).mpr ⟨_, isKostantPartition_single P b hi⟩

/-- Every Kostant partition of a simple root is its singleton partition. -/
theorem eq_single_of_isKostantPartition_root_of_mem_support [DecidableEq ι] {i : ι}
    (hi : i ∈ b.support) {c : ι → ℕ} (hc : IsKostantPartition P b (P.root i) c) :
    c = Pi.single i 1 := by
  -- Total height one forces exactly one positive root to occur, with multiplicity one.
  have hipos : i ∈ posRoots P b := support_subset_posRoots P b hi
  have hheight : ∑ k ∈ posRootsFinset P b, (c k : ℤ) * b.height k = 1 := by
    rw [sum_natCast_mul_height_eq_of_isKostantPartition hc (isKostantPartition_single P b hipos),
      Finset.sum_eq_single_of_mem i ((mem_posRootsFinset P b i).mpr hipos)
        fun k _ hk ↦ by simp [Pi.single_eq_of_ne hk]]
    simp [b.height_one_of_mem_support hi]
  -- the multiplicities sum to at most one
  have hle : (∑ k ∈ posRootsFinset P b, (c k : ℤ)) ≤ 1 := by
    rw [← hheight]
    refine Finset.sum_le_sum fun k hk ↦ le_mul_of_one_le_right (Int.natCast_nonneg _)
      (one_le_height_of_mem_posRoots P b ((mem_posRootsFinset P b k).mp hk))
  have hleNat : ∑ k ∈ posRootsFinset P b, c k ≤ 1 := by exact_mod_cast hle
  -- and they are not all zero, since the simple root is nonzero
  have hne : ∑ k ∈ posRootsFinset P b, c k ≠ 0 := by
    intro h
    refine P.ne_zero i ?_
    rw [← hc.2, Finset.sum_eq_zero]
    intro k hk
    rw [Finset.sum_eq_zero_iff.mp h k hk, zero_smul]
  have hsum : ∑ k ∈ posRootsFinset P b, c k = 1 := by omega
  -- so exactly one multiplicity is nonzero, and it equals one, by `Finsupp.sum_eq_one_iff` read
  -- through the identification of `ι → ℕ` with `ι →₀ ℕ`
  have : Fintype ι := Fintype.ofFinite ι
  have hd : (Finsupp.equivFunOnFinite.symm c).sum (fun _ n ↦ n) = 1 := by
    rw [Finsupp.equivFunOnFinite_symm_sum, ← hsum]
    refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk ↦ ?_).symm
    by_contra h
    exact hk ((mem_posRootsFinset P b k).mpr (hc.1 (mem_support.mpr h)))
  obtain ⟨k₀, hk₀⟩ := (Finsupp.sum_eq_one_iff _).mp hd
  have hcsingle : c = Pi.single k₀ 1 := by
    simpa using congrArg (⇑Finsupp.equivFunOnFinite) hk₀
  have hk₀mem : k₀ ∈ posRootsFinset P b :=
    (mem_posRootsFinset P b k₀).mpr (hc.1 (mem_support.mpr (by simp [hcsingle])))
  -- finally the chosen root is the simple root itself
  have hroot : P.root i = P.root k₀ := by
    rw [← hc.2, hcsingle,
      Finset.sum_eq_single_of_mem k₀ hk₀mem fun k _ hk ↦ by simp [Pi.single_eq_of_ne hk]]
    simp
  rw [hcsingle, P.root.injective hroot]

/-- `P(αᵢ) = 1` for a simple root `αᵢ`. -/
@[simp] theorem kostantPartition_root_of_mem_support {i : ι} (hi : i ∈ b.support) :
    kostantPartition P b (P.root i) = 1 := by
  classical
  have hipos : i ∈ posRoots P b := support_subset_posRoots P b hi
  rw [kostantPartition_def, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y ↦ Subtype.ext ?_⟩, ⟨⟨_, isKostantPartition_single P b hipos⟩⟩⟩
  exact (eq_single_of_isKostantPartition_root_of_mem_support P b hi x.2).trans
    (eq_single_of_isKostantPartition_root_of_mem_support P b hi y.2).symm

end TauCeti
