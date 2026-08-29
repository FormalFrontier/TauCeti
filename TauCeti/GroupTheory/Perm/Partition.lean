/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cycle types that count fixed points

`Equiv.Perm.cycleType σ` lists the lengths of the cycles of `σ` that are at least two, so it
forgets the fixed points and is a partition of `σ.support.card` rather than of the ambient
cardinality. The factorization type of a polynomial modulo a prime is, by contrast, a partition
of the degree that keeps its parts equal to one. The corrected invariant

`σ.cycleType + Multiset.replicate (Fintype.card α - σ.support.card) 1`

is already in Mathlib: it is `(Equiv.Perm.partition σ).parts`, the multiset of parts of
`Equiv.Perm.partition`, and `Equiv.Perm.parts_partition` is its defining equation. This file adds
the API that a comparison with a multiset of factor degrees needs, on that multiset.

## Main results

* `Equiv.Perm.count_one_parts_partition`, `Equiv.Perm.count_parts_partition_of_ne_one`: the parts
  equal to one are the fixed points of `σ`, and at every value other than one the multiset counts a
  part as often as `Equiv.Perm.cycleType` does. Together with Mathlib's
  `Equiv.Perm.filter_parts_partition_eq_cycleType` these say that no information is gained or
  lost.
* `Equiv.Perm.parts_partition_eq_cycleType_iff`: the correction is trivial exactly for a
  permutation with no fixed point.
* `Equiv.Perm.parts_partition_conj`: the multiset is constant on conjugacy classes.
* `Equiv.Perm.lcm_parts_partition`, `Equiv.Perm.sign_of_parts_partition`: the order and the sign
  of a permutation, read off the corrected multiset. These are the two invariants that a single
  exhibited factorization type contributes to the group that exhibits it.
* `Equiv.Perm.parts_partition_permCongr`: transport along an equivalence `α ≃ β` of the underlying
  types leaves it unchanged. Its ingredient `Equiv.Perm.cycleType_permCongr` is proved here too,
  since Mathlib records only `Equiv.Perm.sign_permCongr`. The form for `Equiv.permCongrHom`, the
  group isomorphism a relabelling induces, needs no separate lemma: Mathlib's `simp` lemma
  `Equiv.permCongrHom_coe` rewrites it to `Equiv.permCongr`.
* `Equiv.Perm.parts_partition_of_isCycle`, `Equiv.Perm.parts_partition_swap`: the values on a cycle
  and on a transposition, which are the two shapes the low-degree recognition theorems read.

## Implementation notes

Nothing here introduces a new object. The roadmap below writes `fullCycleType σ` for this
multiset and asks for a definition, but `Equiv.Perm.partition` already carries it with the same
`[Fintype α] [DecidableEq α]` arguments, so a definition would be a wrapper around
`(Equiv.Perm.partition σ).parts` with a `rfl` comparison lemma, and the positivity of the parts
(`Nat.Partition.parts_pos`), the partition sum (`Nat.Partition.parts_sum`), the filter lemma
(`Equiv.Perm.filter_parts_partition_eq_cycleType`) and the completeness of the conjugacy invariant
(`Equiv.Perm.partition_eq_of_isConj`) would each be restated once more. Downstream statements use
`(Equiv.Perm.partition σ).parts`, which is a bare `Multiset ℕ` and so can be compared with a
multiset of factor degrees directly; it is the bundled `σ.partition`, whose type `Nat.Partition n`
is indexed by the ambient cardinality, that cannot.

Since `Equiv.Perm.partition` takes the `DecidableEq α` of its carrier as an instance argument and
is not `noncomputable`, the multiset below is written at the carrier's own instance rather than at
`Classical.propDecidable`, which is what the downstream comparison with a factorization type is
stated with.

The declarations are stated in the `Equiv.Perm` namespace, as upstream candidates and so that they
are found by `simp` and by dot notation alongside Mathlib's own partition lemmas.

This supplies a Layer 0 milestone of `TauCetiRoadmap/PolynomialGaloisGroups/README.md`,
"`fullCycleType`, with its basic API".
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-! ### The two halves of the multiset -/

/-- The parts of `Equiv.Perm.partition` equal to one are the fixed points of `σ`. Together with
`Equiv.Perm.filter_parts_partition_eq_cycleType`, which recovers the cycle lengths, this says that
the correction neither gains nor loses information. -/
@[simp]
theorem _root_.Equiv.Perm.count_one_parts_partition (σ : Equiv.Perm α) :
    σ.partition.parts.count 1 = Fintype.card α - σ.support.card := by
  rw [parts_partition, Multiset.count_add, Multiset.count_replicate_self,
    Multiset.count_eq_zero_of_notMem fun h => (one_lt_of_mem_cycleType h).false, zero_add]

/-- At every value other than one, `Equiv.Perm.partition` counts a part as often as
`Equiv.Perm.cycleType` does. -/
@[simp]
theorem _root_.Equiv.Perm.count_parts_partition_of_ne_one (σ : Equiv.Perm α) {n : ℕ} (hn : n ≠ 1) :
    σ.partition.parts.count n = σ.cycleType.count n := by
  simp [parts_partition, Multiset.count_replicate, hn.symm]

/-- The number of parts of `Equiv.Perm.partition` is the number of cycles of `σ` of length at
least two together with its fixed points. -/
@[simp]
theorem _root_.Equiv.Perm.card_parts_partition (σ : Equiv.Perm α) :
    Multiset.card σ.partition.parts =
      Multiset.card σ.cycleType + (Fintype.card α - σ.support.card) := by
  rw [parts_partition, Multiset.card_add, Multiset.card_replicate]

/-! ### The correction term -/

/-- The correction is trivial exactly when the permutation has no fixed point. This is the one
place where the parts of `Equiv.Perm.partition` and `Equiv.Perm.cycleType` may be exchanged, and
the hypothesis is about `σ`, not about the ambient type. -/
theorem _root_.Equiv.Perm.parts_partition_eq_cycleType_iff {σ : Equiv.Perm α} :
    σ.partition.parts = σ.cycleType ↔ σ.support = Finset.univ := by
  constructor
  · intro h
    have hsum := σ.partition.parts_sum
    rw [h, sum_cycleType] at hsum
    exact Finset.eq_univ_of_card _ hsum
  · intro h
    rw [parts_partition, h, Finset.card_univ, Nat.sub_self, Multiset.replicate_zero, add_zero]

/-- For a permutation with no fixed point, the parts of `Equiv.Perm.partition` are
`Equiv.Perm.cycleType`. -/
theorem _root_.Equiv.Perm.parts_partition_eq_cycleType {σ : Equiv.Perm α}
    (hσ : σ.support = Finset.univ) : σ.partition.parts = σ.cycleType :=
  parts_partition_eq_cycleType_iff.2 hσ

/-! ### Special values -/

/-- The parts of the identity permutation are all one, with one part for each element of the
underlying finite type. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_one :
    (1 : Equiv.Perm α).partition.parts = Multiset.replicate (Fintype.card α) 1 := by
  rw [parts_partition, cycleType_one, support_one, Finset.card_empty, Nat.sub_zero, zero_add]

/-- The identity is the only permutation all of whose parts are one. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_eq_replicate_one_iff {σ : Equiv.Perm α} :
    σ.partition.parts = Multiset.replicate (Fintype.card α) 1 ↔ σ = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, parts_partition_one]⟩
  rw [← cycleType_eq_zero, ← filter_parts_partition_eq_cycleType, h, Multiset.filter_eq_nil]
  exact fun n hn => by rw [Multiset.eq_of_mem_replicate hn]; omega

/-- The cycle type of a cycle, with its fixed points restored. -/
theorem _root_.Equiv.Perm.parts_partition_of_isCycle {σ : Equiv.Perm α} (hσ : σ.IsCycle) :
    σ.partition.parts =
      σ.support.card ::ₘ Multiset.replicate (Fintype.card α - σ.support.card) 1 := by
  rw [parts_partition, hσ.cycleType, Multiset.singleton_add]

/-- The cycle type of a transposition, with its fixed points restored: on a type with `n` points
a transposition has parts `{2, 1, …, 1}` with `n - 2` parts equal to one. -/
theorem _root_.Equiv.Perm.parts_partition_swap {x y : α} (hxy : x ≠ y) :
    (swap x y).partition.parts = 2 ::ₘ Multiset.replicate (Fintype.card α - 2) 1 := by
  rw [parts_partition_of_isCycle (isCycle_swap hxy), card_support_swap hxy]

/-- On an empty type there is nothing to partition. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_of_isEmpty [IsEmpty α] (σ : Equiv.Perm α) :
    σ.partition.parts = 0 := by
  have hσ : σ = 1 := Equiv.ext fun x => isEmptyElim x
  rw [hσ, parts_partition_one, Fintype.card_eq_zero, Multiset.replicate_zero]

/-- The parts of `Equiv.Perm.partition` are empty exactly on an empty type; in particular they do
not vanish on the identity of a nonempty type, unlike `Equiv.Perm.cycleType`. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_eq_zero_iff {σ : Equiv.Perm α} :
    σ.partition.parts = 0 ↔ Fintype.card α = 0 := by
  refine ⟨fun h => by rw [← σ.partition.parts_sum, h, Multiset.sum_zero], fun h => ?_⟩
  have : IsEmpty α := Fintype.card_eq_zero_iff.1 h
  exact parts_partition_of_isEmpty σ

/-! ### Conjugacy -/

/-- The parts of `Equiv.Perm.partition` are constant on conjugacy classes. This is the unbundled
form of Mathlib's `Equiv.Perm.partition_eq_of_isConj`, which also gives the converse. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_conj (g σ : Equiv.Perm α) :
    (g * σ * g⁻¹).partition.parts = σ.partition.parts :=
  congrArg Nat.Partition.parts (partition_eq_of_isConj.1 (isConj_iff.2 ⟨g, rfl⟩)).symm

/-- Inverting a permutation does not change the parts of its partition. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_inv (σ : Equiv.Perm α) :
    σ⁻¹.partition.parts = σ.partition.parts := by
  rw [parts_partition, parts_partition, cycleType_inv, support_inv]

/-! ### Order and parity

The two invariants that a single exhibited factorization type contributes: the order of the
permutation it exhibits, which divides the order of any group containing it, and its sign. -/

private theorem lcm_replicate_one (k : ℕ) : (Multiset.replicate k 1).lcm = 1 :=
  Nat.dvd_one.1 <| Multiset.lcm_dvd.2 fun _ hb => dvd_of_eq (Multiset.eq_of_mem_replicate hb)

/-- The order of a permutation is the least common multiple of the parts of
`Equiv.Perm.partition`. The parts equal to one contribute nothing, so this agrees with
`Equiv.Perm.lcm_cycleType`; stating it here means that a factorization type can be read as a lower
bound on the order of a group directly, without first discarding its fixed points. -/
@[simp]
theorem _root_.Equiv.Perm.lcm_parts_partition (σ : Equiv.Perm α) :
    σ.partition.parts.lcm = orderOf σ := by
  rw [parts_partition, Multiset.lcm_add, lcm_cycleType, lcm_replicate_one]
  simp

/-- Every part of a permutation's partition divides the order of the permutation. -/
theorem _root_.Equiv.Perm.dvd_of_mem_parts_partition {σ : Equiv.Perm α} {n : ℕ}
    (hn : n ∈ σ.partition.parts) : n ∣ orderOf σ := by
  rw [← lcm_parts_partition]
  exact Multiset.dvd_lcm hn

/-- The sign of a permutation, read off the parts of `Equiv.Perm.partition`: it is the parity of
the number of parts, corrected by the ambient cardinality. This is `Equiv.Perm.sign_of_cycleType`
in the convention that keeps the fixed points, and the parity invariant of a Galois image is
computed from it. -/
theorem _root_.Equiv.Perm.sign_of_parts_partition (σ : Equiv.Perm α) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (Fintype.card α + Multiset.card σ.partition.parts) := by
  have hle : σ.support.card ≤ Fintype.card α := by
    simpa using σ.support.card_le_univ
  have h : Fintype.card α + Multiset.card σ.partition.parts =
      σ.cycleType.sum + Multiset.card σ.cycleType + 2 * (Fintype.card α - σ.support.card) := by
    rw [card_parts_partition, sum_cycleType]
    omega
  rw [h, pow_add, pow_mul, sign_of_cycleType]
  simp

/-! ### Transport along an equivalence of the underlying types -/

/-- The cycle type of a permutation does not change when the underlying type is relabelled.
Mathlib has this for `Equiv.Perm.sign` as `Equiv.Perm.sign_permCongr`, and for the extension of a
permutation to a larger type as `Equiv.Perm.cycleType_extendDomain`; relabelling is the case of
the latter in which the predicate cut out is `True`. -/
@[simp]
theorem _root_.Equiv.Perm.cycleType_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  have h : e.permCongr σ =
      σ.extendDomain (e.trans (Equiv.subtypeUnivEquiv (fun _ : β => trivial)).symm) := by
    ext b
    rw [Perm.extendDomain_apply_subtype _ _ trivial]
    simp
  rw [h, cycleType_extendDomain]

/-- Relabelling the underlying type does not change the number of points that a permutation
moves. -/
@[simp]
theorem _root_.Equiv.Perm.card_support_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).support.card = σ.support.card := by
  rw [← sum_cycleType, ← sum_cycleType, cycleType_permCongr]

/-- The parts of `Equiv.Perm.partition` are natural in the underlying type: a relabelling
`e : α ≃ β` leaves them unchanged. This is what lets a statement about the roots of a polynomial,
which form a type with no chosen numbering, be compared with a statement about `Fin n`. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).partition.parts = σ.partition.parts := by
  rw [parts_partition, parts_partition, cycleType_permCongr, card_support_permCongr,
    Fintype.card_congr e]

/-! ### Worked examples

The three shapes that the degree-four recognition theorems read off a factorization type. -/

example : (1 : Equiv.Perm (Fin 4)).partition.parts = {1, 1, 1, 1} := by decide

example : (swap 0 1 : Equiv.Perm (Fin 4)).partition.parts = {2, 1, 1} := by decide

example : (finRotate 4).partition.parts = {4} := by decide

end TauCeti
