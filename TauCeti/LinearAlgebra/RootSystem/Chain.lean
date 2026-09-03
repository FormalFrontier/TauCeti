/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Push
import TauCeti.Data.Fin.Basic

public section

/-!
# Chains with simple or double edges

The diagrams that the classification of finite-type Cartan matrices has to weigh are built out of
**chains**. This file isolates the entry functions for a simply-laced chain and for a chain whose
last edge may be double, together with the summation identities used by weighting arguments.

Nothing here mentions `TauCeti.IsFiniteType`, which is why the file sits above the finite-type
directory rather than in it. It exists because the diagrams that carry the length constraints of
the classification - the stars of `TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Basic`, the
double-edge chains of `TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Basic`, and the
forked double-edge diagrams of `TauCeti.LinearAlgebra.RootSystem.FiniteType.ForkedDoubleEdge` -
are all assembled from chains and are all excluded by a vector that is linear along each chain
they contain. The simply-laced entry function and row sum are the special case `L = 0` of their
type-`B` counterparts.

## Main definitions

* `TauCeti.chainEntry`: the Cartan-matrix entry of a chain between two positions along it.
* `TauCeti.chainBEntry`: the Cartan-matrix entry of a chain whose last edge may be double.

## Main results

* `TauCeti.chainEntry_eq_cartanMatrix_A`: a chain of `n` positions is Mathlib's Cartan matrix of
  type `Aₙ`, which is what makes the name of the entry function the right one.
* `TauCeti.sum_range_chainEntry_mul`: the row of a chain at a position, evaluated at a weight `g`.
  Away from the two ends it is the second difference `2 g (m + 1) - g m - g (m + 2)`, so a weight
  that is linear in the position is annihilated there.
* `TauCeti.sum_range_chainEntry_mul_affine`: the resulting formula for an affine weight.
* `TauCeti.sum_range_chainBEntry_mul`: the corresponding row sum with a double last edge.
## References

The chain weighting is the calculation of J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §11.4, and Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §4.
-/

namespace TauCeti

/-- The Cartan-matrix entry of a **chain of type `B`** between the positions `s` and `t`, the last
position being `L`: `2` on the diagonal, `-1` between consecutive positions, and `-2` from the
position before `L` to `L` itself, whose root is the short one.

A value of `L` outside the range of positions describes a simply-laced chain, of type `A`; `L = 0`
is the convenient such value, since no position is the successor of `0`. -/
def chainBEntry (L s t : ℕ) : ℤ :=
  if s = t then 2 else if s + 1 = t then (if t = L then -2 else -1)
  else if t + 1 = s then -1 else 0

-- `(rfl)`, not `rfl`: the body of `TauCeti.chainBEntry` is deliberately left unexposed, and the
-- parenthesised form keeps this equation out of the exported definitional-equality check.
/-- The entries of a chain of type `B`, spelled out: this is how a file that has to case on all of
them at once reaches the definition, whose body is not exposed. -/
lemma chainBEntry_def (L s t : ℕ) :
    chainBEntry L s t = if s = t then 2 else if s + 1 = t then (if t = L then -2 else -1)
      else if t + 1 = s then -1 else 0 := (rfl)

@[simp] lemma chainBEntry_self (L s : ℕ) : chainBEntry L s s = 2 := by
  unfold chainBEntry; split_ifs <;> omega

/-- Stepping forwards along the chain crosses a double edge exactly at the short end. -/
@[simp] lemma chainBEntry_succ_right (L s : ℕ) :
    chainBEntry L s (s + 1) = if s + 1 = L then -2 else -1 := by
  unfold chainBEntry; split_ifs <;> omega

/-- Stepping backwards along the chain always crosses a single edge: the short root is the target
of the double edge, not its source. -/
@[simp] lemma chainBEntry_succ_left (L s : ℕ) : chainBEntry L (s + 1) s = -1 := by
  unfold chainBEntry; split_ifs <;> omega

/-- Away from the diagonal and its two neighbours a chain has no entry. -/
@[simp] lemma chainBEntry_eq_zero {L s t : ℕ} (h1 : s ≠ t) (h2 : s + 1 ≠ t)
    (h3 : t + 1 ≠ s) :
    chainBEntry L s t = 0 := by
  unfold chainBEntry; split_ifs <;> omega

/-- A chain of type `B` is Mathlib's Cartan matrix of type `B`: on `n` positions the two entry
rules agree. -/
lemma chainBEntry_eq_cartanMatrix_B {n : ℕ} (i j : Fin n) :
    chainBEntry (n - 1) i j = CartanMatrix.B n i j := by
  simp only [CartanMatrix.B, chainBEntry_def, Matrix.of_apply, Fin.ext_iff]

/-- **A single entry of a chain of type `B`, against a weight, split into its three positions.**
The entry at `(a, s)` contributes only when `s` is `a`, its predecessor, or its successor, and the
successor contribution is doubled at the short end.

The identity is pointwise in `s`: it mentions neither the summation range of the row it is used in
nor any bound on `a`. The last position `L` does appear, in the doubled coefficient at the short
end. -/
private theorem chainBEntry_mul_eq_add_add {R : Type*} [NonAssocRing R] (L a s : ℕ) (g : ℕ → R) :
    ((chainBEntry L a s : ℤ) : R) * g s
      = (if s = a then 2 * g a else 0) + (if s + 1 = a then -g s else 0)
        + (if s = a + 1 then -((if a + 1 = L then 2 else 1) * g (a + 1)) else 0) := by
  -- the four cases `s = a`, `s + 1 = a`, `s = a + 1` and otherwise each pin the entry
  rcases eq_or_ne s a with rfl | h1
  · rw [chainBEntry_self]
    split_ifs <;> first | (exfalso; omega) | (push_cast; noncomm_ring)
  rcases eq_or_ne (s + 1) a with rfl | h2
  · rw [chainBEntry_succ_left]
    split_ifs <;> first | (exfalso; omega) | (push_cast; noncomm_ring)
  rcases eq_or_ne s (a + 1) with rfl | h3
  · rw [chainBEntry_succ_right]
    split_ifs <;> first | (exfalso; omega) | (push_cast; noncomm_ring)
  · rw [chainBEntry_eq_zero (Ne.symm h1) (fun h ↦ h3 h.symm) h2]
    split_ifs <;> first | (exfalso; omega) | (push_cast; noncomm_ring)

/-- **A row of a chain of type `B`, against an arbitrary weighting of its positions.** The row `a`
collects `2 g a`, the weight of the position before it - absent at the head of the chain - and the
weight of the position after it, doubled when that position is the short end and absent when the row
is the short end itself. Only ring operations and integer casts are used. -/
theorem sum_range_chainBEntry_mul {R : Type*} [NonAssocRing R] {L m a : ℕ} (ha : a < m)
    (g : ℕ → R) :
    ∑ s ∈ Finset.range m, (chainBEntry L a s : R) * g s
      = 2 * g a - (if a = 0 then 0 else g (a - 1))
        - (if a + 1 = m then 0 else (if a + 1 = L then 2 else 1) * g (a + 1)) := by
  rw [Finset.sum_congr rfl (fun s _ ↦ chainBEntry_mul_eq_add_add L a s g),
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : ∑ s ∈ Finset.range m, (if s = a then 2 * g a else 0) = 2 * g a := by
    rw [Finset.sum_ite_eq' (Finset.range m) a fun _ ↦ 2 * g a]
    simp [Finset.mem_range, ha]
  have h3 : ∑ s ∈ Finset.range m,
      (if s = a + 1 then -((if a + 1 = L then 2 else 1) * g (a + 1)) else 0)
      = -(if a + 1 = m then 0 else (if a + 1 = L then 2 else 1) * g (a + 1)) := by
    rw [Finset.sum_ite_eq' (Finset.range m) (a + 1)
      fun _ ↦ -((if a + 1 = L then 2 else 1) * g (a + 1))]
    by_cases hm : a + 1 = m
    · simp [Finset.mem_range, hm]
    · rw [ite_eq_left (Finset.mem_range.2 (by omega)), ite_eq_right hm]
  have h2 : ∑ s ∈ Finset.range m, (if s + 1 = a then -g s else 0)
      = -(if a = 0 then 0 else g (a - 1)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    have hcond : (a - 1 < m ∧ 1 ≤ a) ↔ a ≠ 0 := by omega
    simpa [eq_comm, hcond, neg_ite] using sum_ite_val_add (n := m) (fun i : Fin m ↦ -g i) a 1
  rw [h1, h2, h3]
  noncomm_ring

/-- The Cartan-matrix entry of a **chain** between the positions `s` and `t` along it: `2` on the
diagonal, `-1` between consecutive positions, and `0` otherwise. A chain is simply laced, so this
single function describes all of its edges. -/
def chainEntry (s t : ℕ) : ℤ :=
  chainBEntry 0 s t

-- `(rfl)`, not `rfl`: the body of `TauCeti.chainEntry` is deliberately left unexposed, and the
-- parenthesised form keeps this equation out of the exported definitional-equality check.
lemma chainEntry_def (s t : ℕ) :
    chainEntry s t = if s = t then 2 else if s = t + 1 then -1 else if t = s + 1 then -1 else 0 :=
  by unfold chainEntry chainBEntry; split_ifs <;> omega

@[simp] lemma chainEntry_self (s : ℕ) : chainEntry s s = 2 := chainBEntry_self 0 s

@[simp] lemma chainEntry_succ_left (s : ℕ) : chainEntry (s + 1) s = -1 := by
  exact chainBEntry_succ_left 0 s

@[simp] lemma chainEntry_succ_right (s : ℕ) : chainEntry s (s + 1) = -1 := by
  rw [chainEntry, chainBEntry_succ_right]
  omega

/-- Away from the diagonal and its two neighbours a chain has no entry. -/
@[simp] lemma chainEntry_eq_zero {s t : ℕ} (h1 : s ≠ t) (h2 : s ≠ t + 1) (h3 : t ≠ s + 1) :
    chainEntry s t = 0 := by
  exact chainBEntry_eq_zero h1 (fun h ↦ h3 h.symm) (fun h ↦ h2 h.symm)

/-- Shifting both positions of a chain by one leaves the entry unchanged: only the difference of
the positions matters. This is not a `simp` lemma: it would rewrite the right-hand sides of the
entry lemmas for `TauCeti.starCartanMatrix`, whose arm positions are shifted by one against the
centre, out of the form those lemmas state. -/
lemma chainEntry_succ_succ (s t : ℕ) : chainEntry (s + 1) (t + 1) = chainEntry s t := by
  rw [chainEntry_def, chainEntry_def]
  split_ifs <;> omega

/-- A chain is symmetric: the entry depends on the unordered pair of positions. -/
lemma chainEntry_comm (s t : ℕ) : chainEntry s t = chainEntry t s := by
  rw [chainEntry_def, chainEntry_def]
  split_ifs <;> omega

/-- A chain is Mathlib's Cartan matrix of type `A`: on `n` positions the two entry rules agree. -/
lemma chainEntry_eq_cartanMatrix_A {n : ℕ} (i j : Fin n) :
    chainEntry i j = CartanMatrix.A n i j := by
  rw [chainEntry_def]
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- **The row of a chain, evaluated at a weight.** Along `n` positions `1, …, n`, carrying the
weights `g 1, …, g n`, the entries at the position `m` collect `2 g (m + 1) - g m - g (m + 2)`, the
term `g m` being absent at `m = 0` and the term `g (m + 2)` at the far end. A weight that is linear
in the position is therefore annihilated away from the two ends.

The offset by one in the argument of `g` leaves room for a further vertex at the position `0`,
which is how both diagrams that consume this identity attach a chain to the rest of themselves.

Only the ring operations and the integer cast of the entries are used, so the weight may take its
values in any ring; the diagrams weigh their vertices by rational numbers. -/
theorem sum_range_chainEntry_mul {R : Type*} [Ring R] {n m : ℕ} (hm : m < n) (g : ℕ → R) :
    ∑ s ∈ Finset.range n, (chainEntry m s : R) * g (s + 1)
      = 2 * g (m + 1) - (if m = 0 then 0 else g m)
        - (if m + 1 = n then 0 else g (m + 2)) := by
  by_cases h0 : m = 0
  · subst m
    simpa [chainEntry] using
      (sum_range_chainBEntry_mul (L := 0) hm (fun s ↦ g (s + 1)))
  · have h1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr h0
    simpa [chainEntry, h0, Nat.sub_add_cancel h1, Nat.add_assoc] using
      (sum_range_chainBEntry_mul (L := 0) hm (fun s ↦ g (s + 1)))

/-- **A row of a chain evaluated at an affine weight.** Interior rows vanish; the first row leaves
`b - a`, the last row leaves `a * n + b`, and the unique row of a one-vertex chain leaves `2 * b`.
-/
theorem sum_range_chainEntry_mul_affine {R : Type*} [Ring R] {n m : ℕ} (hm : m < n)
    (a b : R) :
    ∑ s ∈ Finset.range n, (chainEntry m s : R) * (a * (s : R) + b) =
      if m = 0 then (if m + 1 = n then 2 * b else b - a)
      else if m + 1 = n then a * (n : R) + b else 0 := by
  have hrow := sum_range_chainEntry_mul hm
    (fun u : ℕ ↦ a * ((u - 1 : ℕ) : R) + b)
  simp only [Nat.add_sub_cancel] at hrow
  rw [hrow]
  by_cases hzero : m = 0
  · subst m
    by_cases hend : 1 = n
    · subst n
      simp
    · simp only [Nat.cast_zero, mul_zero, zero_add, hend, ite_false, ite_true]
      push_cast
      noncomm_ring
  · have hpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hzero
    by_cases hend : m + 1 = n
    · subst n
      simp only [hzero, ite_false, Nat.cast_sub hpos, Nat.cast_add, Nat.cast_one, ite_true]
      noncomm_ring
    · simp only [hzero, hend, ite_false, Nat.cast_sub hpos, Nat.cast_one]
      push_cast
      noncomm_ring

end TauCeti
