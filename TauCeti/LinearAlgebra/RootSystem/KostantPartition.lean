/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Positive

/-!
# The Kostant partition function

The Kostant partition function `P(ν)` counts the ways of writing an element `ν` of the weight
space as a sum of positive roots with multiplicity. This file defines it for a base of an
arbitrary root pairing, together with the finiteness statement that makes the count meaningful.

The multiplicities are recorded as a function `c : ι → ℕ` on root indices, supported on the
positive roots, and `TauCeti.IsKostantPartition P b ν c` says that `∑ᵢ cᵢ αᵢ = ν`. There are
infinitely many functions `ι → ℕ` even for a finite index type, so the count is a theorem rather
than a definition: `TauCeti.finite_setOf_isKostantPartition` bounds the multiplicities of a
partition by the height of `ν`, and only then is `TauCeti.kostantPartition` a natural number.

The bound comes from a fact about heights that is worth isolating, since it has nothing to do with
positivity: `TauCeti.sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero` says that height respects
every integral relation among roots, so the total height `∑ᵢ cᵢ ht(αᵢ)` depends only on `ν` and not
on the partition. Each positive root has height at least one, so a partition of `ν` cannot use more
than `ht(ν)` roots in all, and in particular no multiplicity exceeds `ht(ν)`.

## Main definitions

* `TauCeti.IsKostantPartition`: the predicate that a multiplicity function writes `ν` as a sum of
  positive roots.
* `TauCeti.kostantPartition`: the Kostant partition function, the number of such multiplicity
  functions.

## Main results

* `TauCeti.sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero`: heights respect integral relations
  among roots.
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

/-! ## Height and integral relations among roots -/

/-- **Height respects integral relations among roots.** If an integral combination of roots
vanishes, then the same combination of their heights vanishes.

Expanding each root in the simple roots turns the relation into one among the simple roots, whose
coefficients then vanish by linear independence; summing those coefficients over the simple roots
recovers the combination of heights, because the height of a root is by definition the sum of its
simple coordinates. -/
theorem sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero {s : Finset ι} {e : ι → ℤ}
    (he : ∑ i ∈ s, e i • P.root i = 0) :
    ∑ i ∈ s, e i * b.height i = 0 := by
  classical
  choose g _hgsupp _hgsign hg using fun i : ι ↦ b.exists_root_eq_sum_int i
  have hcomb : ∑ j ∈ b.support, (∑ i ∈ s, e i * g i j) • P.root j = 0 := by
    rw [← he]
    simp_rw [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← Finset.smul_sum, ← hg i]
  have hczero : ∀ j ∈ b.support, (∑ i ∈ s, e i * g i j) = 0 :=
    linearIndepOn_iff'.mp (b.linearIndepOn_root.restrict_scalars' ℤ) b.support
      (fun j ↦ ∑ i ∈ s, e i * g i j) subset_rfl hcomb
  calc ∑ i ∈ s, e i * b.height i
      = ∑ i ∈ s, ∑ j ∈ b.support, e i * g i j :=
        Finset.sum_congr rfl fun i _ ↦ by rw [b.height_eq_sum (hg i), Finset.mul_sum]
    _ = ∑ j ∈ b.support, ∑ i ∈ s, e i * g i j := Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero hczero

/-- Two integral combinations of roots with the same value have the same combination of heights:
the height of an element of the root lattice does not depend on how it is written. -/
theorem sum_mul_height_eq_of_sum_zsmul_root_eq {s : Finset ι} {e f : ι → ℤ}
    (h : ∑ i ∈ s, e i • P.root i = ∑ i ∈ s, f i • P.root i) :
    ∑ i ∈ s, e i * b.height i = ∑ i ∈ s, f i * b.height i := by
  have h0 : ∑ i ∈ s, (e i - f i) • P.root i = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have key := sum_mul_height_eq_zero_of_sum_zsmul_root_eq_zero P b h0
  simp_rw [sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at key
  exact key

/-- A positive root has height at least one, its height being a positive integer. -/
theorem one_le_height_of_mem_posRoots {i : ι} (hi : i ∈ posRoots P b) : 1 ≤ b.height i := by
  have h : b.IsPos i := (mem_posRoots P b i).mp hi
  rw [RootPairing.Base.isPos_iff] at h
  omega

/-! ## Kostant partitions -/

variable [Finite ι]

/-- **A Kostant partition of `ν`**: a multiplicity function `c` on root indices, supported on the
positive roots, whose weighted sum of positive roots is `ν`. -/
def IsKostantPartition (ν : M) (c : ι → ℕ) : Prop :=
  support c ⊆ posRoots P b ∧ ∑ i ∈ posRootsFinset P b, c i • P.root i = ν

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

/-- Every term of the total height of a multiplicity function is nonnegative. -/
theorem natCast_mul_height_nonneg (c : ι → ℕ) (i : ι) (hi : i ∈ posRootsFinset P b) :
    0 ≤ (c i : ℤ) * b.height i := by
  have h := one_le_height_of_mem_posRoots P b ((mem_posRootsFinset P b i).mp hi)
  exact mul_nonneg (Int.natCast_nonneg _) (by omega)

/-- **Each multiplicity is bounded by the total height.** Positive roots have height at least one,
so a single multiplicity never exceeds the whole weighted height sum. -/
theorem natCast_le_sum_natCast_mul_height (c : ι → ℕ) {i : ι} (hi : i ∈ posRootsFinset P b) :
    (c i : ℤ) ≤ ∑ k ∈ posRootsFinset P b, (c k : ℤ) * b.height k := by
  refine le_trans ?_ (Finset.single_le_sum (natCast_mul_height_nonneg P b c) hi)
  exact le_mul_of_one_le_right (Int.natCast_nonneg _)
    (one_le_height_of_mem_posRoots P b ((mem_posRootsFinset P b i).mp hi))

/-- **An element has only finitely many Kostant partitions.** If there is one, its total height
bounds every multiplicity of every other one, so all of them lie in a fixed finite box. -/
theorem finite_setOf_isKostantPartition (ν : M) :
    {c : ι → ℕ | IsKostantPartition P b ν c}.Finite := by
  by_cases hne : ∃ c₀, IsKostantPartition P b ν c₀
  · obtain ⟨c₀, hc₀⟩ := hne
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

/-- The Kostant partitions of an element form a finite type, which is what makes the Kostant
partition function below a natural number. -/
instance instFiniteSubtypeIsKostantPartition (ν : M) :
    Finite {c : ι → ℕ // IsKostantPartition P b ν c} :=
  (finite_setOf_isKostantPartition P b ν).to_subtype

/-- **The Kostant partition function** `P(ν)`: the number of ways of writing `ν` as a sum of
positive roots with multiplicity. -/
noncomputable def kostantPartition (ν : M) : ℕ :=
  Nat.card {c : ι → ℕ // IsKostantPartition P b ν c}

/-- The Kostant partition function is positive exactly on the elements that are a sum of positive
roots. -/
theorem kostantPartition_pos_iff (ν : M) :
    0 < kostantPartition P b ν ↔ ∃ c, IsKostantPartition P b ν c := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ ?_⟩
  · obtain ⟨⟨c, hc⟩⟩ := (Nat.card_pos_iff.mp h).1
    exact ⟨c, hc⟩
  · have : Nonempty {c : ι → ℕ // IsKostantPartition P b ν c} := ⟨⟨c, hc⟩⟩
    exact Nat.card_pos

/-- The Kostant partition function vanishes exactly off the set of sums of positive roots. -/
theorem kostantPartition_eq_zero_iff (ν : M) :
    kostantPartition P b ν = 0 ↔ ¬ ∃ c, IsKostantPartition P b ν c := by
  rw [← kostantPartition_pos_iff, Nat.pos_iff_ne_zero, not_ne_iff]

/-! ## The two smallest values -/

/-- **The empty partition is the only partition of zero.** A nonzero multiplicity would contribute
a positive amount to the total height, which is zero. -/
theorem isKostantPartition_zero_iff {c : ι → ℕ} : IsKostantPartition P b (0 : M) c ↔ c = 0 := by
  refine ⟨fun hc ↦ ?_, ?_⟩
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
  rw [kostantPartition, Nat.card_eq_one_iff_unique]
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

/-- **A simple root is a sum of positive roots in only the obvious way.** Every positive root has
height at least one and the simple root has height one, so a partition of it uses exactly one root,
with multiplicity one; that root then has the same root vector, hence the same index. -/
theorem isKostantPartition_root_eq_single_of_mem_support [DecidableEq ι] {i : ι}
    (hi : i ∈ b.support) {c : ι → ℕ} (hc : IsKostantPartition P b (P.root i) c) :
    c = Pi.single i 1 := by
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
  -- so exactly one multiplicity is nonzero, and it equals one
  obtain ⟨k₀, hk₀mem, hk₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hsplit := Finset.add_sum_erase (posRootsFinset P b) c hk₀mem
  rw [hsum] at hsplit
  have hck₀ : c k₀ = 1 := by omega
  have herase : ∀ k ∈ (posRootsFinset P b).erase k₀, c k = 0 := by
    refine Finset.sum_eq_zero_iff.mp ?_
    omega
  have hcsingle : c = Pi.single k₀ 1 := by
    funext k
    by_cases hkk : k = k₀
    · rw [hkk, hck₀, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hkk]
      by_cases hk : k ∈ posRootsFinset P b
      · exact herase k (Finset.mem_erase.mpr ⟨hkk, hk⟩)
      · by_contra h
        exact hk ((mem_posRootsFinset P b k).mpr (hc.1 (mem_support.mpr h)))
  -- finally the chosen root is the simple root itself
  have hroot : P.root i = P.root k₀ := by
    rw [← hc.2, hcsingle,
      Finset.sum_eq_single_of_mem k₀ hk₀mem fun k _ hk ↦ by simp [Pi.single_eq_of_ne hk]]
    simp
  rw [hcsingle, P.root.injective hroot]

/-- `P(αᵢ) = 1` for a simple root `αᵢ`. -/
theorem kostantPartition_root_of_mem_support {i : ι} (hi : i ∈ b.support) :
    kostantPartition P b (P.root i) = 1 := by
  classical
  have hipos : i ∈ posRoots P b := support_subset_posRoots P b hi
  rw [kostantPartition, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y ↦ Subtype.ext ?_⟩, ⟨⟨_, isKostantPartition_single P b hipos⟩⟩⟩
  exact (isKostantPartition_root_eq_single_of_mem_support P b hi x.2).trans
    (isKostantPartition_root_eq_single_of_mem_support P b hi y.2).symm

end TauCeti
