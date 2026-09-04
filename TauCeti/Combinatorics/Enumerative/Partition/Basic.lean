/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Named partitions

This file records some partitions of `n` that are referred to by name.  Two of them are the
extremes: `Nat.Partition.ones n = (1ⁿ)`, the finest partition, into `n` parts equal to `1`, is the
opposite extreme to Mathlib's coarsest partition `Nat.Partition.indiscrete n = (n)`, whose parts
are the single part `n` when `n ≠ 0`, and none when `n = 0`.  The third is
`Nat.Partition.singletonSecondRow n = (n+1, 1)`, the partition of `n+2` with two parts whose
second part is a single box; it is written at `n+2` so that both parts are positive with no
hypothesis on `n`.
-/

public section

namespace TauCeti

namespace Nat.Partition

/-- The partition `(1ⁿ)` of `n` into `n` parts, each equal to `1`.

This is the finest partition of `n`, opposite to Mathlib's coarsest `Nat.Partition.indiscrete n`,
whose parts are the single part `n` when `n ≠ 0`, and none when `n = 0`.

The parts are exposed only through `Nat.Partition.ones_parts`. -/
def ones (n : ℕ) : n.Partition :=
  _root_.Nat.Partition.ofSums n (Multiset.replicate n 1) (by simp)

@[simp]
theorem ones_parts (n : ℕ) : (ones n).parts = Multiset.replicate n 1 := by
  simp [ones, Multiset.filter_eq_self, Multiset.mem_replicate]

/-- The product of the factorials of the parts of the coarsest partition `(n)` is `n !`.

For `n = 0` this is the empty product, and `0! = 1` agrees with it. -/
@[simp]
theorem prod_map_factorial_indiscrete (n : ℕ) :
    ((_root_.Nat.Partition.indiscrete n).parts.map Nat.factorial).prod = n.factorial := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp [_root_.Nat.Partition.indiscrete_parts hn.ne']

/-- The partition `(n+1, 1)` of `n+2`: two parts, the second a single box.

This is the shape usually written `(n-1, 1)` at `n`; writing it at `n+2` keeps both parts positive
with no hypothesis on `n`.  It is the unique shape with two rows whose second row is a single box,
and the coarsest shape other than `Nat.Partition.indiscrete`.

The parts are exposed only through `Nat.Partition.singletonSecondRow_parts`. -/
def singletonSecondRow (n : ℕ) : (n + 2).Partition :=
  _root_.Nat.Partition.ofSums (n + 2) {n + 1, 1} (by simp)

/-- The parts of `(n+1, 1)`. -/
@[simp]
theorem singletonSecondRow_parts (n : ℕ) : (singletonSecondRow n).parts = {n + 1, 1} := by
  simp [singletonSecondRow, Multiset.filter_eq_self]

/-- The decreasingly sorted parts of `(n+1, 1)`. -/
theorem sort_parts_singletonSecondRow (n : ℕ) :
    (singletonSecondRow n).parts.sort (· ≥ ·) = [n + 1, 1] := by
  rw [singletonSecondRow_parts, Multiset.insert_eq_cons,
    Multiset.sort_cons _ _ _ (by simp), Multiset.sort_singleton]

end Nat.Partition

end TauCeti
