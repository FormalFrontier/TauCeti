/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cycle types that count fixed points

`Equiv.Perm.cycleType σ` lists the lengths of the cycles of `σ` that are at least two, so it
forgets the fixed points and is a partition of `σ.support.card` rather than of the ambient
cardinality. The factorization type of a polynomial modulo a prime is, by contrast, a partition
of the degree that keeps its parts equal to one. This file introduces the corrected invariant

`TauCeti.fullCycleType σ = σ.cycleType + Multiset.replicate (Fintype.card α - σ.support.card) 1`

and gives it the API that a comparison with a multiset of factor degrees needs.

## Main definitions

* `TauCeti.fullCycleType`: the cycle type of a permutation of a finite type, with one part equal
  to `1` for each fixed point.

## Main results

* `TauCeti.sum_fullCycleType`: the parts sum to `Fintype.card α`, so `fullCycleType` is a
  partition of the ambient cardinality.
* `TauCeti.filter_fullCycleType`, `TauCeti.count_one_fullCycleType`: the parts that are at least
  two are exactly `Equiv.Perm.cycleType`, and the remaining parts are the fixed points. Together
  these say that no information is gained or lost.
* `TauCeti.fullCycleType_eq_cycleType_iff`: the correction is trivial exactly for a permutation
  with no fixed point.
* `TauCeti.isConj_iff_fullCycleType_eq`: `fullCycleType` is a complete invariant of the conjugacy
  class, so in particular it is constant on conjugacy classes.
* `TauCeti.lcm_fullCycleType`, `TauCeti.sign_eq_of_fullCycleType`: the order and the sign of a
  permutation, read off the corrected multiset. These are the two invariants that a single
  exhibited factorization type contributes to the group that exhibits it.
* `TauCeti.fullCycleType_permCongr`: transport along an equivalence `α ≃ β` of the underlying
  types leaves it unchanged. Its ingredient `Equiv.Perm.cycleType_permCongr` is proved here too,
  since Mathlib records only `Equiv.Perm.sign_permCongr`.
* `TauCeti.fullCycleType_of_isCycle`, `TauCeti.fullCycleType_swap`: the values on a cycle and on a
  transposition, which are the two shapes the low-degree recognition theorems read.

## Implementation notes

Mathlib's `Equiv.Perm.partition` bundles the same multiset as a term of `Nat.Partition`, and
`TauCeti.fullCycleType_eq_parts_partition` records that the two agree definitionally; the proofs
below take the positivity of the parts and the completeness of the invariant from that bundling
rather than repeating them. What the bundled form cannot do is be compared with a multiset of
factor degrees without projecting first, and `Nat.Partition n` is indexed by the ambient
cardinality `n`, so a hypothesis relating two such cardinalities has to be transported before two
partitions can even be stated to be equal. The unbundled multiset is the object every downstream
statement wants.

The `DecidableEq α` argument is deliberate, and `fullCycleType` is not `noncomputable`: closing
the definition over `Classical.propDecidable` produces a multiset that is equal, but not
syntactically equal, to the same multiset written at the carrier's own instance, and the
downstream comparison with a factorization type is stated at the latter.

This supplies a Layer 0 milestone of `TauCetiRoadmap/PolynomialGaloisGroups/README.md`,
"`fullCycleType`, with its basic API".
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The cycle type of a permutation of a finite type, corrected to count its fixed points:
`Equiv.Perm.cycleType` records only the cycle lengths that are at least two, and
`fullCycleType` appends one part equal to `1` for every point that `σ` fixes. It is therefore a
partition of `Fintype.card α`, which is the shape in which a factorization type of a polynomial
of degree `Fintype.card α` presents itself. -/
@[expose] def fullCycleType (σ : Equiv.Perm α) : Multiset ℕ :=
  σ.cycleType + Multiset.replicate (Fintype.card α - σ.support.card) 1

theorem fullCycleType_def (σ : Equiv.Perm α) :
    fullCycleType σ = σ.cycleType + Multiset.replicate (Fintype.card α - σ.support.card) 1 :=
  rfl

/-- `fullCycleType` is the multiset of parts of Mathlib's `Equiv.Perm.partition`, on the nose. -/
theorem fullCycleType_eq_parts_partition (σ : Equiv.Perm α) :
    fullCycleType σ = σ.partition.parts :=
  rfl

/-! ### The two halves of the multiset -/

/-- The parts of `fullCycleType` that are at least two are the cycle lengths of `σ`. -/
theorem filter_fullCycleType (σ : Equiv.Perm α) :
    (fullCycleType σ).filter (fun n => 2 ≤ n) = σ.cycleType :=
  filter_parts_partition_eq_cycleType

/-- The parts of `fullCycleType` equal to one are the fixed points of `σ`. -/
theorem count_one_fullCycleType (σ : Equiv.Perm α) :
    (fullCycleType σ).count 1 = Fintype.card α - σ.support.card := by
  rw [fullCycleType_def, Multiset.count_add, Multiset.count_replicate_self,
    Multiset.count_eq_zero_of_notMem fun h => (one_lt_of_mem_cycleType h).false, zero_add]

/-- Away from the value one, `fullCycleType` counts a part as often as `Equiv.Perm.cycleType`
does. -/
theorem count_fullCycleType_of_two_le (σ : Equiv.Perm α) {n : ℕ} (hn : 2 ≤ n) :
    (fullCycleType σ).count n = σ.cycleType.count n := by
  have h1 : (1 : ℕ) ≠ n := by omega
  simp [fullCycleType_def, Multiset.count_replicate, h1]

/-- Every part of `fullCycleType` is positive: the parts of `Equiv.Perm.cycleType` are at least
two, and the parts that were added for the fixed points are one. -/
theorem pos_of_mem_fullCycleType {σ : Equiv.Perm α} {n : ℕ} (hn : n ∈ fullCycleType σ) : 0 < n :=
  σ.partition.parts_pos hn

/-- `fullCycleType` is a partition of the cardinality of the ambient type, and not merely of the
number of points that the permutation moves. This is the property that makes it comparable with
the multiset of degrees of the irreducible factors of a polynomial. -/
@[simp]
theorem sum_fullCycleType (σ : Equiv.Perm α) : (fullCycleType σ).sum = Fintype.card α :=
  σ.partition.parts_sum

/-- The number of parts of `fullCycleType` is the number of cycles of `σ` of length at least two
together with its fixed points. -/
theorem card_fullCycleType (σ : Equiv.Perm α) :
    Multiset.card (fullCycleType σ) =
      Multiset.card σ.cycleType + (Fintype.card α - σ.support.card) := by
  rw [fullCycleType_def, Multiset.card_add, Multiset.card_replicate]

/-! ### The correction term -/

/-- The correction is trivial exactly when the permutation has no fixed point. This is the one
place where `fullCycleType` and `Equiv.Perm.cycleType` may be exchanged, and the hypothesis is
about `σ`, not about the ambient type. -/
theorem fullCycleType_eq_cycleType_iff {σ : Equiv.Perm α} :
    fullCycleType σ = σ.cycleType ↔ σ.support = Finset.univ := by
  constructor
  · intro h
    have hsum := sum_fullCycleType σ
    rw [h, sum_cycleType] at hsum
    exact Finset.eq_univ_of_card _ hsum
  · intro h
    rw [fullCycleType_def, h, Finset.card_univ, Nat.sub_self, Multiset.replicate_zero, add_zero]

/-- For a permutation with no fixed point, `fullCycleType` is `Equiv.Perm.cycleType`. -/
theorem fullCycleType_eq_cycleType {σ : Equiv.Perm α} (hσ : σ.support = Finset.univ) :
    fullCycleType σ = σ.cycleType :=
  fullCycleType_eq_cycleType_iff.2 hσ

/-! ### Special values -/

@[simp]
theorem fullCycleType_one : fullCycleType (1 : Equiv.Perm α) = Multiset.replicate
    (Fintype.card α) 1 := by
  rw [fullCycleType_def, cycleType_one, support_one, Finset.card_empty, Nat.sub_zero, zero_add]

/-- The identity is the only permutation all of whose parts are one. -/
theorem fullCycleType_eq_replicate_one_iff {σ : Equiv.Perm α} :
    fullCycleType σ = Multiset.replicate (Fintype.card α) 1 ↔ σ = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, fullCycleType_one]⟩
  rw [← cycleType_eq_zero, ← filter_fullCycleType, h, Multiset.filter_eq_nil]
  exact fun n hn => by rw [Multiset.eq_of_mem_replicate hn]; omega

/-- The cycle type of a cycle, with its fixed points restored. -/
theorem fullCycleType_of_isCycle {σ : Equiv.Perm α} (hσ : σ.IsCycle) :
    fullCycleType σ =
      σ.support.card ::ₘ Multiset.replicate (Fintype.card α - σ.support.card) 1 := by
  rw [fullCycleType_def, hσ.cycleType, Multiset.singleton_add]

/-- The cycle type of a transposition, with its fixed points restored: on a type with `n` points
a transposition has full cycle type `{2, 1, …, 1}` with `n - 2` parts equal to one. -/
theorem fullCycleType_swap {x y : α} (hxy : x ≠ y) :
    fullCycleType (swap x y) = 2 ::ₘ Multiset.replicate (Fintype.card α - 2) 1 := by
  rw [fullCycleType_of_isCycle (isCycle_swap hxy), card_support_swap hxy]

/-- On an empty type there is nothing to partition. -/
@[simp]
theorem fullCycleType_of_isEmpty [IsEmpty α] (σ : Equiv.Perm α) : fullCycleType σ = 0 := by
  have hσ : σ = 1 := Equiv.ext fun x => isEmptyElim x
  rw [hσ, fullCycleType_one, Fintype.card_eq_zero, Multiset.replicate_zero]

/-- `fullCycleType` is empty exactly on an empty type; in particular it does not vanish on the
identity of a nonempty type, unlike `Equiv.Perm.cycleType`. -/
theorem fullCycleType_eq_zero_iff {σ : Equiv.Perm α} :
    fullCycleType σ = 0 ↔ Fintype.card α = 0 := by
  refine ⟨fun h => by rw [← sum_fullCycleType σ, h, Multiset.sum_zero], fun h => ?_⟩
  have : IsEmpty α := Fintype.card_eq_zero_iff.1 h
  exact fullCycleType_of_isEmpty σ

/-! ### Conjugacy -/

/-- `fullCycleType` is a complete invariant of conjugacy, exactly as `Equiv.Perm.cycleType` is.
Since it also determines the ambient cardinality through `TauCeti.sum_fullCycleType`, this is the
statement that a factorization type recognises a conjugacy class of permutations. -/
theorem isConj_iff_fullCycleType_eq {σ τ : Equiv.Perm α} :
    IsConj σ τ ↔ fullCycleType σ = fullCycleType τ := by
  rw [partition_eq_of_isConj, Nat.Partition.ext_iff]
  rfl

/-- `fullCycleType` is constant on conjugacy classes. -/
@[simp]
theorem fullCycleType_conj (g σ : Equiv.Perm α) :
    fullCycleType (g * σ * g⁻¹) = fullCycleType σ :=
  (isConj_iff_fullCycleType_eq.1 (isConj_iff.2 ⟨g, rfl⟩)).symm

@[simp]
theorem fullCycleType_inv (σ : Equiv.Perm α) : fullCycleType σ⁻¹ = fullCycleType σ := by
  rw [fullCycleType_def, fullCycleType_def, cycleType_inv, support_inv]

/-! ### Order and parity

The two invariants that a single exhibited factorization type contributes: the order of the
permutation it exhibits, which divides the order of any group containing it, and its sign. -/

private theorem lcm_replicate_one (k : ℕ) : (Multiset.replicate k 1).lcm = 1 :=
  Nat.dvd_one.1 <| Multiset.lcm_dvd.2 fun _ hb => dvd_of_eq (Multiset.eq_of_mem_replicate hb)

/-- The order of a permutation is the least common multiple of its full cycle type. The parts
equal to one contribute nothing, so this agrees with `Equiv.Perm.lcm_cycleType`; stating it here
means that a factorization type can be read as a lower bound on the order of a group directly,
without first discarding its fixed points. -/
@[simp]
theorem lcm_fullCycleType (σ : Equiv.Perm α) : (fullCycleType σ).lcm = orderOf σ := by
  rw [fullCycleType_def, Multiset.lcm_add, lcm_cycleType, lcm_replicate_one]
  simp

theorem dvd_of_mem_fullCycleType {σ : Equiv.Perm α} {n : ℕ} (hn : n ∈ fullCycleType σ) :
    n ∣ orderOf σ := by
  rw [← lcm_fullCycleType]
  exact Multiset.dvd_lcm hn

/-- The sign of a permutation, read off its full cycle type: it is the parity of the number of
parts, corrected by the ambient cardinality. This is `Equiv.Perm.sign_of_cycleType` in the
convention that keeps the fixed points, and the parity invariant of a Galois image is computed
from it. -/
theorem sign_eq_of_fullCycleType (σ : Equiv.Perm α) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (Fintype.card α + Multiset.card (fullCycleType σ)) := by
  have hle : σ.support.card ≤ Fintype.card α := by
    simpa using σ.support.card_le_univ
  have h : Fintype.card α + Multiset.card (fullCycleType σ) =
      σ.cycleType.sum + Multiset.card σ.cycleType + 2 * (Fintype.card α - σ.support.card) := by
    rw [card_fullCycleType, sum_cycleType]
    omega
  rw [h, pow_add, pow_mul, sign_of_cycleType]
  simp

/-! ### Transport along an equivalence of the underlying types -/

/-- The cycle type of a permutation does not change when the underlying type is relabelled.
Mathlib has this for `Equiv.Perm.sign` as `Equiv.Perm.sign_permCongr`, and for the extension of a
permutation to a larger type as `Equiv.Perm.cycleType_extendDomain`; relabelling is the case of
the latter in which the predicate cut out is `True`. -/
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
theorem _root_.Equiv.Perm.card_support_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).support.card = σ.support.card := by
  rw [← sum_cycleType, ← sum_cycleType, cycleType_permCongr]

/-- `fullCycleType` is natural in the underlying type: a relabelling `e : α ≃ β` leaves it
unchanged. This is what lets a statement about the roots of a polynomial, which form a type with
no chosen numbering, be compared with a statement about `Fin n`. -/
@[simp]
theorem fullCycleType_permCongr (e : α ≃ β) (σ : Equiv.Perm α) :
    fullCycleType (e.permCongr σ) = fullCycleType σ := by
  rw [fullCycleType_def, fullCycleType_def, cycleType_permCongr, card_support_permCongr,
    Fintype.card_congr e]

/-- The form of `TauCeti.fullCycleType_permCongr` stated for `Equiv.permCongrHom`, which is the
group isomorphism `Equiv.Perm α ≃* Equiv.Perm β` that a relabelling induces. It is not marked
`@[simp]`: `simp` already unfolds `Equiv.permCongrHom` to `Equiv.permCongr` through
`Equiv.permCongrHom_coe`, and then `TauCeti.fullCycleType_permCongr` applies. -/
theorem fullCycleType_permCongrHom (e : α ≃ β) (σ : Equiv.Perm α) :
    fullCycleType (e.permCongrHom σ) = fullCycleType σ := by
  rw [show e.permCongrHom σ = e.permCongr σ from rfl, fullCycleType_permCongr]

/-! ### Worked examples

The three shapes that the degree-four recognition theorems read off a factorization type. -/

example : fullCycleType (1 : Equiv.Perm (Fin 4)) = {1, 1, 1, 1} := by decide

example : fullCycleType (swap 0 1 : Equiv.Perm (Fin 4)) = {2, 1, 1} := by decide

example : fullCycleType (finRotate 4) = {4} := by decide

end TauCeti
