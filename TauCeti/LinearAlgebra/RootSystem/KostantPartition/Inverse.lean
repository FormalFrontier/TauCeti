/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.KostantPartition.Basic

/-!
# The Kostant partition function inverts the Weyl denominator

The Weyl denominator `Δ = ∏_{α > 0} (1 - e^{-α})` of `TauCeti.weylDenominator` expands, by
`TauCeti.weylDenominator_eq_sum_powerset`, as the signed sum
`∑_{T ⊆ Φ⁺} (-1)^{|T|} e^{-∑_{α ∈ T} α}` over the subsets of the positive roots. Formally inverting
each factor, `(1 - e^{-α})⁻¹ = ∑_{k ≥ 0} e^{-kα}`, gives the series `∑_ν P(ν) e^{-ν}` whose
coefficients are the Kostant partition function `TauCeti.kostantPartition`. This file proves that
the two are indeed inverse, in the only form in which the statement makes sense inside the honest
group algebra `ℤ[M]`: coefficient by coefficient,

`∑_{T ⊆ Φ⁺} (-1)^{|T|} P(ν - ∑_{α ∈ T} α) = δ_{ν, 0}`.

Both sides are finite. The series `∑_ν P(ν) e^{-ν}` itself is not an element of `ℤ[M]` as soon as
there is a positive root, so no statement of the form `Δ * K = 1` is available without a completion;
the identity above is what such a statement would say about the coefficient at `-ν`, and it is what
the applications use. Read with `ν = λ - x`, it says that the character of a module whose weight
multiplicities are the values `P(λ - x)`, which is what a Verma module `M(λ)` has, satisfies
`ch M(λ) · Δ = e^λ`; read directly, it is the expansion of the inverse denominator against which
the Weyl character formula is developed into Kostant's multiplicity formula.

## The argument

The proof is an induction over the set of positive roots that are allowed to occur, which forces a
relative version of the partition function: `TauCeti.kostantPartitionOn P b S ν` counts the Kostant
partitions of `ν` whose multiplicities are supported in a subset `S` of the positive roots, so that
`S = Φ⁺` recovers `TauCeti.kostantPartition` and `S = ∅` leaves only the empty partition of `0`.

The step is the recursion `TauCeti.kostantPartitionOn_eq_erase_add_sub_root`: for `i ∈ S`, a
partition supported in `S` either does not use `αᵢ`, and is a partition supported in `S` with `i`
erased, or uses it, and then raising the multiplicity of `αᵢ` by one matches the partitions that use
it bijectively with the partitions of `ν - αᵢ` supported in `S`. Splitting the sum over subsets of
`insert i S` into those subsets containing `i` and those not turns the alternating sum into a sum of
differences `P_S(ν - σ) - P_S(ν - σ - αᵢ)`, which the recursion identifies with the values of the
partition function of `S` with `i` erased, and the induction hypothesis applies.

## Main definitions

* `TauCeti.IsKostantPartitionOn` and `TauCeti.kostantPartitionOn`: the Kostant partitions whose
  multiplicities are supported in a prescribed set of positive roots, and their number.

## Main results

* `TauCeti.kostantPartitionOn_eq_erase_add_sub_root`: the recursion in the set of allowed roots.
* `TauCeti.sum_powerset_neg_one_pow_mul_kostantPartitionOn` and
  `TauCeti.sum_powerset_neg_one_pow_mul_kostantPartition`: **the inversion identity**, the second
  being the case `S = Φ⁺` that inverts the Weyl denominator.

## Roadmap

The Kostant partition function is asked for in Layer 3 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, to be consumed by the Verma weight
multiplicities of that layer and by Kostant's multiplicity formula in Layer 6, whose stated proof is
"by expanding the character formula against the geometric-series expansion of the inverse
denominator (whose coefficients are `P`)". This file is that expansion. As with
`TauCeti.weylDenominator` and `TauCeti.kostantPartition`, nothing here uses the Lie algebra, so it
is stated for a base of an arbitrary root pairing.

## References

* B. Kostant, *A formula for the multiplicity of a weight*, Trans. Amer. Math. Soc. **93** (1959).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §24.2.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter VIII, §9.
-/

public section

namespace TauCeti

open Function Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [CharZero R]
  (P : RootPairing ι R M N) (b : P.Base) [Finite ι]

/-! ## Kostant partitions supported in a set of positive roots -/

/-- **A Kostant partition of `ν` supported in `S`**: a Kostant partition of `ν` all of whose
multiplicities are carried by the root indices in `S`. -/
def IsKostantPartitionOn (S : Finset ι) (ν : M) (c : ι → ℕ) : Prop :=
  IsKostantPartition P b ν c ∧ support c ⊆ (S : Set ι)

/-- A multiplicity function is a Kostant partition supported in `S` exactly when it is a Kostant
partition and is supported in `S`. -/
theorem isKostantPartitionOn_iff (S : Finset ι) (ν : M) (c : ι → ℕ) :
    IsKostantPartitionOn P b S ν c ↔ IsKostantPartition P b ν c ∧ support c ⊆ (S : Set ι) :=
  Iff.rfl

/-- The Kostant partitions supported in a set form a finite type, so their `Nat.card` is their
finite cardinality. -/
instance instFiniteSubtypeIsKostantPartitionOn (S : Finset ι) (ν : M) :
    Finite {c : ι → ℕ // IsKostantPartitionOn P b S ν c} :=
  Finite.of_injective (fun c ↦ (⟨c.1, c.2.1⟩ : {c : ι → ℕ // IsKostantPartition P b ν c}))
    fun _ _ h ↦ Subtype.ext congr(($h).1)

/-- **The Kostant partition function of a set of positive roots** `P_S(ν)`: the number of ways of
writing `ν` as a sum, with multiplicity, of the positive roots indexed by `S`. -/
noncomputable def kostantPartitionOn (S : Finset ι) (ν : M) : ℕ :=
  Nat.card {c : ι → ℕ // IsKostantPartitionOn P b S ν c}

/-- The relative Kostant partition function counts the Kostant partitions supported in its set. -/
theorem kostantPartitionOn_def (S : Finset ι) (ν : M) :
    kostantPartitionOn P b S ν = Nat.card {c : ι → ℕ // IsKostantPartitionOn P b S ν c} := by
  rw [kostantPartitionOn]

/-- Being supported in the whole set of positive roots is no condition at all. -/
@[simp] theorem isKostantPartitionOn_posRootsFinset_iff {ν : M} {c : ι → ℕ} :
    IsKostantPartitionOn P b (posRootsFinset P b) ν c ↔ IsKostantPartition P b ν c :=
  ⟨And.left, fun h ↦ ⟨h, fun i hi ↦ Finset.mem_coe.mpr ((mem_posRootsFinset P b i).mpr
    (((isKostantPartition_iff P b ν c).mp h).1 hi))⟩⟩

/-- **The relative Kostant partition function of the full set of positive roots is the Kostant
partition function.** -/
@[simp] theorem kostantPartitionOn_posRootsFinset (ν : M) :
    kostantPartitionOn P b (posRootsFinset P b) ν = kostantPartition P b ν := by
  rw [kostantPartitionOn_def, kostantPartition_def]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun _ ↦ isKostantPartitionOn_posRootsFinset_iff P b)

/-- The only Kostant partition using no positive root at all is the empty partition of `0`. -/
@[simp] theorem isKostantPartitionOn_empty_iff {ν : M} {c : ι → ℕ} :
    IsKostantPartitionOn P b (∅ : Finset ι) ν c ↔ c = 0 ∧ ν = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hc : c = 0 := support_eq_empty_iff.mp
      (subset_empty_iff.mp (by simpa using h.2))
    exact ⟨hc, by simpa [hc] using (((isKostantPartition_iff P b ν c).mp h.1).2).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨(isKostantPartition_zero_iff P b).mpr rfl, by simp⟩

open Classical in
/-- **`P_∅(ν)` is `1` at `0` and `0` elsewhere**: the base case of the inversion identity. -/
@[simp] theorem kostantPartitionOn_empty (ν : M) :
    kostantPartitionOn P b (∅ : Finset ι) ν = if ν = 0 then 1 else 0 := by
  rw [kostantPartitionOn_def]
  split_ifs with hν
  · rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y ↦ Subtype.ext ?_⟩, ⟨⟨0, (isKostantPartitionOn_empty_iff P b).mpr ⟨rfl, hν⟩⟩⟩⟩
    exact ((isKostantPartitionOn_empty_iff P b).mp x.2).1.trans
      ((isKostantPartitionOn_empty_iff P b).mp y.2).1.symm
  · have : IsEmpty {c : ι → ℕ // IsKostantPartitionOn P b (∅ : Finset ι) ν c} :=
      ⟨fun x ↦ hν ((isKostantPartitionOn_empty_iff P b).mp x.2).2⟩
    exact Nat.card_of_isEmpty

/-! ## The recursion in the set of allowed roots -/

variable {P b}

/-- Raising the multiplicity of the positive root `αᵢ` by one adds `αᵢ` to the element that a
multiplicity function represents. -/
private theorem sum_smul_root_add_single [DecidableEq ι] {i : ι} (hi : i ∈ posRootsFinset P b)
    (c : ι → ℕ) :
    ∑ k ∈ posRootsFinset P b, (c + Pi.single i 1 : ι → ℕ) k • P.root k
      = (∑ k ∈ posRootsFinset P b, c k • P.root k) + P.root i := by
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single_of_mem i hi fun k _ hk ↦ by simp [Pi.single_eq_of_ne hk]]
  simp

/-- Raising the multiplicity of a positive root `αᵢ` of `S` by one carries a Kostant partition of
`ν - αᵢ` supported in `S` to one of `ν` supported in `S`. -/
private theorem isKostantPartitionOn_add_single [DecidableEq ι] {S : Finset ι} {i : ι} (hiS : i ∈ S)
    (hi : i ∈ posRootsFinset P b) {ν : M} {c : ι → ℕ}
    (hc : IsKostantPartitionOn P b S (ν - P.root i) c) :
    IsKostantPartitionOn P b S ν (c + Pi.single i 1) := by
  have hne : ∀ j ≠ i, j ∈ support (c + Pi.single i 1 : ι → ℕ) → c j ≠ 0 := by
    intro j hji hj hcj
    exact mem_support.mp hj (by simp [hcj, Pi.single_eq_of_ne hji])
  refine ⟨(isKostantPartition_iff P b _ _).mpr ⟨fun j hj ↦ ?_, ?_⟩, fun j hj ↦ ?_⟩
  · by_cases hji : j = i
    · exact hji ▸ (mem_posRootsFinset P b i).mp hi
    · exact ((isKostantPartition_iff P b _ _).mp hc.1).1 (mem_support.mpr (hne j hji hj))
  · rw [sum_smul_root_add_single hi c, ((isKostantPartition_iff P b _ _).mp hc.1).2,
      sub_add_cancel]
  · by_cases hji : j = i
    · exact hji ▸ Finset.mem_coe.mpr hiS
    · exact hc.2 (mem_support.mpr (hne j hji hj))

/-- Lowering the multiplicity of a positive root `αᵢ` that a Kostant partition of `ν` supported in
`S` uses produces a Kostant partition of `ν - αᵢ` supported in `S`. -/
private theorem exists_add_single_eq [DecidableEq ι] {S : Finset ι} {i : ι}
    (hi : i ∈ posRootsFinset P b) {ν : M} {x : ι → ℕ} (hx : IsKostantPartitionOn P b S ν x)
    (hxi : x i ≠ 0) :
    ∃ c, IsKostantPartitionOn P b S (ν - P.root i) c ∧ c + Pi.single i 1 = x := by
  have hx1 : 1 ≤ x i := Nat.one_le_iff_ne_zero.mpr hxi
  have hadd : (fun j ↦ x j - (Pi.single i 1 : ι → ℕ) j) + Pi.single i 1 = x := by
    funext j
    by_cases hji : j = i <;> simp [hji, Pi.single_eq_of_ne, hx1]
  have hsupp : ∀ j, j ∈ support (fun j ↦ x j - (Pi.single i 1 : ι → ℕ) j) → j ∈ support x :=
    fun j hj ↦ mem_support.mpr fun h ↦ mem_support.mp hj (by simp [h])
  refine ⟨_, ⟨(isKostantPartition_iff P b _ _).mpr ⟨fun j hj ↦ ?_, ?_⟩, fun j hj ↦ ?_⟩, hadd⟩
  · exact ((isKostantPartition_iff P b _ _).mp hx.1).1 (hsupp j hj)
  · have hsum := sum_smul_root_add_single hi (fun j ↦ x j - (Pi.single i 1 : ι → ℕ) j)
    rw [hadd, ((isKostantPartition_iff P b _ _).mp hx.1).2] at hsum
    rw [eq_sub_iff_add_eq, hsum]
  · exact hx.2 (hsupp j hj)

/-- **The recursion for the Kostant partition function in the set of allowed roots.** A partition
supported in `S` either avoids the positive root `αᵢ`, and so is supported in `S` with `i` erased,
or uses it, and then lowering the multiplicity of `αᵢ` by one is a bijection onto the partitions of
`ν - αᵢ` supported in `S`. -/
theorem kostantPartitionOn_eq_erase_add_sub_root [DecidableEq ι] {S : Finset ι} {i : ι}
    (hiS : i ∈ S) (hi : i ∈ posRootsFinset P b) (ν : M) :
    kostantPartitionOn P b S ν
      = kostantPartitionOn P b (S.erase i) ν + kostantPartitionOn P b S (ν - P.root i) := by
  -- The partitions that avoid `αᵢ` are exactly those supported in `S` with `i` erased.
  have herase : ∀ c : ι → ℕ,
      IsKostantPartitionOn P b S ν c ∧ c i = 0 ↔ IsKostantPartitionOn P b (S.erase i) ν c := by
    refine fun c ↦ ⟨fun ⟨hc, hci⟩ ↦ ⟨hc.1, fun j hj ↦ ?_⟩, fun hc ↦ ⟨⟨hc.1, ?_⟩, ?_⟩⟩
    · exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
        ⟨fun hji ↦ mem_support.mp hj (hji ▸ hci), Finset.mem_coe.mp (hc.2 hj)⟩)
    · exact hc.2.trans (by exact_mod_cast Finset.coe_subset.mpr (Finset.erase_subset i S))
    · by_contra hci
      exact (Finset.mem_erase.mp (Finset.mem_coe.mp (hc.2 (mem_support.mpr hci)))).1 rfl
  -- Raising the multiplicity of `αᵢ` is a bijection onto the partitions that use it.
  have hbij : Function.Bijective
      (fun c : {c : ι → ℕ // IsKostantPartitionOn P b S (ν - P.root i) c} ↦
        (⟨c.1 + Pi.single i 1, isKostantPartitionOn_add_single hiS hi c.2, by simp⟩ :
          {c : ι → ℕ // IsKostantPartitionOn P b S ν c ∧ c i ≠ 0})) :=
    ⟨fun c d h ↦ Subtype.ext (add_right_cancel congr(($h).1)), fun x ↦ by
      obtain ⟨c, hc, hcx⟩ := exists_add_single_eq hi x.2.1 x.2.2
      exact ⟨⟨c, hc⟩, Subtype.ext hcx⟩⟩
  -- Splitting the partitions supported in `S` according to whether they use `αᵢ`.
  have esplit : {c : ι → ℕ // IsKostantPartitionOn P b S ν c} ≃
      {c : ι → ℕ // IsKostantPartitionOn P b (S.erase i) ν c} ⊕
        {c : ι → ℕ // IsKostantPartitionOn P b S (ν - P.root i) c} :=
    (Equiv.sumCompl fun c : {c : ι → ℕ // IsKostantPartitionOn P b S ν c} ↦ c.1 i = 0).symm.trans
      (Equiv.sumCongr
        ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans (Equiv.subtypeEquivRight herase))
        ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans (Equiv.ofBijective _ hbij).symm))
  rw [kostantPartitionOn_def, kostantPartitionOn_def, kostantPartitionOn_def,
    Nat.card_congr esplit, Nat.card_sum]

/-! ## The inversion identity -/

variable (P b)

open Classical in
/-- **The Kostant partition function of a set of positive roots inverts the corresponding
denominator.** The alternating sum, over the subsets `T` of `S`, of the number of partitions of
`ν - ∑_{α ∈ T} α` supported in `S` is `1` at `ν = 0` and `0` elsewhere. -/
theorem sum_powerset_neg_one_pow_mul_kostantPartitionOn {S : Finset ι}
    (hS : S ⊆ posRootsFinset P b) (ν : M) :
    ∑ T ∈ S.powerset,
        (-1 : ℤ) ^ T.card * kostantPartitionOn P b S (ν - ∑ i ∈ T, P.root i)
      = if ν = 0 then 1 else 0 := by
  revert hS
  induction S using Finset.induction_on generalizing ν with
  | empty =>
    intro _
    by_cases hν : ν = 0 <;> simp [kostantPartitionOn_empty, hν]
  | @insert i S hi ih =>
    intro hS
    -- A subset of `insert i S` either omits `i`, or is `insert i t` for a subset `t` of `S`.
    have key : ∀ t ∈ S.powerset,
        (-1 : ℤ) ^ t.card *
            kostantPartitionOn P b (insert i S) (ν - ∑ k ∈ t, P.root k)
          + (-1 : ℤ) ^ (insert i t).card *
              kostantPartitionOn P b (insert i S) (ν - ∑ k ∈ insert i t, P.root k)
          = (-1 : ℤ) ^ t.card * kostantPartitionOn P b S (ν - ∑ k ∈ t, P.root k) := by
      intro t ht
      have hit : i ∉ t := fun h ↦ hi (Finset.mem_powerset.mp ht h)
      have hrec := kostantPartitionOn_eq_erase_add_sub_root (Finset.mem_insert_self i S)
        (hS (Finset.mem_insert_self i S)) (ν - ∑ k ∈ t, P.root k)
      rw [Finset.erase_insert hi] at hrec
      -- `Finset.sum_insert` splits off `αᵢ` on the left of the sum, leaving the argument in the
      -- shape `ν - (αᵢ + ∑_{k ∈ t} αₖ)`, whereas the recursion subtracts `αᵢ` from the argument
      -- `ν - ∑_{k ∈ t} αₖ` it is applied at; the two differ only by reassociating the subtraction.
      have hshift : ν - (P.root i + ∑ k ∈ t, P.root k) = (ν - ∑ k ∈ t, P.root k) - P.root i := by
        abel
      rw [Finset.card_insert_of_notMem hit, Finset.sum_insert hit, hshift, hrec]
      push_cast
      ring
    rw [Finset.sum_powerset_insert hi, ← Finset.sum_add_distrib, Finset.sum_congr rfl key]
    exact ih ν ((Finset.subset_insert i S).trans hS)

open Classical in
/-- **The Kostant partition function inverts the Weyl denominator.** Since
`Δ = ∑_{T ⊆ Φ⁺} (-1)^{|T|} e^{-∑_{α ∈ T} α}` by `TauCeti.weylDenominator_eq_sum_powerset`, this is
the statement that the coefficient at `e^{-ν}` of the product of `Δ` with the formal series
`∑_ν P(ν) e^{-ν}` is `1` at `ν = 0` and `0` elsewhere. -/
theorem sum_powerset_neg_one_pow_mul_kostantPartition (ν : M) :
    ∑ T ∈ (posRootsFinset P b).powerset,
        (-1 : ℤ) ^ T.card * kostantPartition P b (ν - ∑ i ∈ T, P.root i)
      = if ν = 0 then 1 else 0 := by
  simpa using sum_powerset_neg_one_pow_mul_kostantPartitionOn P b subset_rfl ν

end TauCeti
