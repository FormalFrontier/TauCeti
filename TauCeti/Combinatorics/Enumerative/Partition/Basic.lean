/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# The finest and coarsest partitions

This file records the partition `Nat.Partition.ones n = (1ⁿ)` into `n` parts equal to `1`, the
opposite extreme to Mathlib's coarsest partition `Nat.Partition.indiscrete n = (n)`, whose parts
are the single part `n` when `n ≠ 0`, and none when `n = 0`.
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

end Nat.Partition

end TauCeti
