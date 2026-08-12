/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

public section

/-!
# The rows of a chain

Every candidate diagram of the Cartan-Killing classification is assembled from chains, and the
eliminations all proceed by evaluating one row of a Cartan matrix against a weighting of the
vertices. This file carries that computation once, for a chain whose last edge is allowed to be a
double edge, so that the files excluding individual families can quote it.

`TauCeti.chainBEntry L s t` is the Cartan-matrix entry of a chain of type `B` between the positions
`s` and `t`, the short root sitting at the position `L`: `2` on the diagonal, `-1` between
consecutive positions, and `-2` from the position before `L` to `L` itself. Choosing `L` outside the
range of positions leaves the simply-laced chain of type `A`; `L = 0` is the convenient such choice,
since no position is the successor of `0`, and it is how
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Star` uses this file.

## Main definitions

* `TauCeti.chainBEntry`: the Cartan-matrix entry of a chain of type `B`.

## Main results

* `TauCeti.sum_range_chainBEntry_mul`: **a row of a chain**, against an arbitrary weighting `g` of
  its positions. The row `a` collects `2 g a`, the weight of the position before `a` - absent at the
  head of the chain - and the weight of the position after `a`, doubled when that position is the
  short end and absent when `a` is the last position.

## References

This file supports the "chain/fork length constraints" step of the classification of finite-type
Cartan matrices, Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The
weighting arguments it serves are those of J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §11.4.
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
lemma chainBEntry_eq_zero {L s t : ℕ} (h1 : s ≠ t) (h2 : s + 1 ≠ t) (h3 : t + 1 ≠ s) :
    chainBEntry L s t = 0 := by
  unfold chainBEntry; split_ifs <;> omega

/-- **A row of a chain of type `B`, against an arbitrary weighting of its positions.** The row `a`
collects `2 g a`, the weight of the position before it - absent at the head of the chain - and the
weight of the position after it, doubled when that position is the short end and absent when the row
is the short end itself. -/
theorem sum_range_chainBEntry_mul {L m a : ℕ} (ha : a < m) (g : ℕ → ℚ) :
    ∑ s ∈ Finset.range m, (chainBEntry L a s : ℚ) * g s
      = 2 * g a - (if a = 0 then 0 else g (a - 1))
        - (if a + 1 = m then 0 else (if a + 1 = L then 2 else 1) * g (a + 1)) := by
  have key : ∀ s ∈ Finset.range m, ((chainBEntry L a s : ℤ) : ℚ) * g s
      = (if s = a then 2 * g a else 0) + (if s + 1 = a then -g s else 0)
        + (if s = a + 1 then -((if a + 1 = L then 2 else 1) * g (a + 1)) else 0) := by
    intro s _
    rcases eq_or_ne s a with rfl | h1
    · rw [chainBEntry_self]
      split_ifs <;> first | (exfalso; omega) | (push_cast; ring)
    rcases eq_or_ne (s + 1) a with rfl | h2
    · rw [chainBEntry_succ_left]
      split_ifs <;> first | (exfalso; omega) | (push_cast; ring)
    rcases eq_or_ne s (a + 1) with rfl | h3
    · rw [chainBEntry_succ_right]
      split_ifs <;> first | (exfalso; omega) | (push_cast; ring)
    · rw [chainBEntry_eq_zero (Ne.symm h1) (fun h ↦ h3 h.symm) h2]
      split_ifs <;> first | (exfalso; omega) | (push_cast; ring)
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib]
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
    match a with
    | 0 => simp
    | k + 1 =>
      have hcongr : ∀ s ∈ Finset.range m, (if s + 1 = k + 1 then -g s else 0)
          = (if s = k then -g k else 0) := by
        intro s _
        by_cases h : s = k <;> simp [h]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' (Finset.range m) k fun _ ↦ -g k,
        ite_eq_left (Finset.mem_range.2 (by omega)), ite_eq_right (Nat.succ_ne_zero k)]
      norm_num
  rw [h1, h2, h3]
  ring

end TauCeti
