/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan
public import Mathlib.Algebra.Order.Field.Rat

public section

/-!
# Chains in a simply-laced diagram

A **chain** is a path: its vertices carry the positions `0, 1, 2, …` and each is joined to its two
neighbours only. `TauCeti.chainEntry` is the Cartan-matrix entry of a chain, `2` on the diagonal
and `-1` between consecutive positions; on `n` positions it is Mathlib's `CartanMatrix.A n`
(`TauCeti.chainEntry_eq_cartanMatrix_A`).

Chains are what the simply-laced diagrams excluded from finite type are built from: the arms of a
star (`TauCeti.LinearAlgebra.RootSystem.FiniteType.Star`) and the spine of a double fork
(`TauCeti.LinearAlgebra.RootSystem.FiniteType.AffineD`) are chains, and both files evaluate a row
of their matrix at a test vector by the same computation, `TauCeti.sum_range_chainEntry_mul`: a row
weighted by a function `g` of the position collects `2 g (m + 1) - g m - g (m + 2)`, the outer
terms being dropped at the two ends of the chain. Its constant-weight case is the row sum of a
type-`A` Cartan matrix, `TauCeti.sum_cartanMatrix_A_row`, which counts the ends of the chain the
row touches.

## Main definitions

* `TauCeti.chainEntry`: the Cartan-matrix entry of a chain, in terms of positions.

## Main results

* `TauCeti.chainEntry_eq_cartanMatrix_A`: a chain on `n` positions is `CartanMatrix.A n`.
* `TauCeti.sum_range_chainEntry_mul`: a weighted row of a chain.
* `TauCeti.sum_cartanMatrix_A_row`: the rows of `CartanMatrix.A n` sum to `1` at each end of the
  chain and to `0` in its interior.

## References

The chain computations here are shared by the diagram obstructions of the “chain/fork length
constraints” step in Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See
J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §11.4, and Bourbaki,
*Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.
-/

namespace TauCeti

/-- The Cartan-matrix entry of a **chain** between the positions `s` and `t` along it: `2` on the
diagonal, `-1` between consecutive positions, and `0` otherwise. A chain is simply laced, so this
single function describes all of its edges. -/
def chainEntry (s t : ℕ) : ℤ :=
  if s = t then 2 else if s = t + 1 then -1 else if t = s + 1 then -1 else 0

-- `(rfl)`, not `rfl`: the body of `chainEntry` is deliberately left unexposed, and the
-- parenthesised form keeps this equation out of the exported definitional-equality check.
/-- The defining equation of `TauCeti.chainEntry`, the entry lemmas below being the shape its
consumers rewrite with. -/
theorem chainEntry_def (s t : ℕ) :
    chainEntry s t = if s = t then 2 else if s = t + 1 then -1 else if t = s + 1 then -1 else 0 :=
  (rfl)

/-- A vertex of a chain has diagonal entry `2`. -/
@[simp] theorem chainEntry_self (s : ℕ) : chainEntry s s = 2 := by simp [chainEntry_def]

/-- Consecutive positions of a chain are joined by a single edge. -/
@[simp] theorem chainEntry_succ_left (s : ℕ) : chainEntry (s + 1) s = -1 := by
  rw [chainEntry_def]; split_ifs <;> omega

/-- Consecutive positions of a chain are joined by a single edge. -/
@[simp] theorem chainEntry_succ_right (s : ℕ) : chainEntry s (s + 1) = -1 := by
  rw [chainEntry_def]; split_ifs <;> omega

/-- Away from the diagonal and its two neighbours a chain has no entry. -/
theorem chainEntry_eq_zero {s t : ℕ} (h1 : s ≠ t) (h2 : s ≠ t + 1)
    (h3 : t ≠ s + 1) :
    chainEntry s t = 0 := by
  rw [chainEntry_def]; split_ifs <;> omega

/-- Shifting both positions of a chain by one leaves the entry unchanged: only the difference of
the positions matters. This is not a `simp` lemma: it would rewrite the right-hand sides of the
entry lemmas for `TauCeti.starCartanMatrix`, whose arm positions are shifted by one against the
centre, out of the form those lemmas state. -/
theorem chainEntry_succ_succ (s t : ℕ) :
    chainEntry (s + 1) (t + 1) = chainEntry s t := by
  rw [chainEntry_def, chainEntry_def]; split_ifs <;> omega

/-- A chain is symmetric: the entry depends on the unordered pair of positions. -/
theorem chainEntry_comm (s t : ℕ) : chainEntry s t = chainEntry t s := by
  rw [chainEntry_def, chainEntry_def]; split_ifs <;> omega

/-- A chain is Mathlib's Cartan matrix of type `A`: on `n` positions the two entry rules agree. -/
theorem chainEntry_eq_cartanMatrix_A {n : ℕ} (i j : Fin n) :
    chainEntry i j = CartanMatrix.A n i j := by
  simp only [chainEntry_def, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- The chain sum, in the shape a row of a diagram built from chains consumes: along `n` positions
`1, …, n`, the entries at the position `m` collect `2 g (m + 1) - g m - g (m + 2)`, the term `g m`
being absent at `m = 0` (where a star has its centre, summed separately) and `g (m + 2)` at the far
end. -/
theorem sum_range_chainEntry_mul {n m : ℕ} (hm : m < n) (g : ℕ → ℚ) :
    ∑ s ∈ Finset.range n, (chainEntry m s : ℚ) * g (s + 1)
      = 2 * g (m + 1) - (if m = 0 then 0 else g m)
        - (if m + 1 = n then 0 else g (m + 2)) := by
  have key : ∀ s ∈ Finset.range n, ((chainEntry m s : ℤ) : ℚ) * g (s + 1)
      = (if s = m then 2 * g (m + 1) else 0) + (if s + 1 = m then -g m else 0)
        + (if s = m + 1 then -g (m + 2) else 0) := by
    intro s _
    by_cases h1 : s = m
    · subst h1
      rw [ite_eq_left rfl, ite_eq_right (by omega : ¬ (s + 1 = s)),
        ite_eq_right (by omega : ¬ (s = s + 1)), chainEntry_self]
      norm_num
    by_cases h2 : s + 1 = m
    · subst h2
      rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right (by omega : ¬ (s = s + 1 + 1)),
        chainEntry_succ_left]
      norm_num
    by_cases h3 : s = m + 1
    · subst h3
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left rfl, chainEntry_succ_right]
      norm_num
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
        chainEntry_eq_zero (fun h ↦ h1 h.symm) (fun h ↦ h2 h.symm) h3]
      norm_num
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : ∑ s ∈ Finset.range n, (if s = m then 2 * g (m + 1) else 0) = 2 * g (m + 1) := by
    rw [Finset.sum_ite_eq' (Finset.range n) m fun _ ↦ 2 * g (m + 1)]
    simp [Finset.mem_range, hm]
  have h3 : ∑ s ∈ Finset.range n, (if s = m + 1 then -g (m + 2) else 0)
      = -(if m + 1 = n then 0 else g (m + 2)) := by
    rw [Finset.sum_ite_eq' (Finset.range n) (m + 1) fun _ ↦ -g (m + 2)]
    by_cases hn : m + 1 = n
    · simp [Finset.mem_range, hn]
    · rw [ite_eq_left (Finset.mem_range.2 (by omega)), ite_eq_right hn]
  have h2 : ∑ s ∈ Finset.range n, (if s + 1 = m then -g m else 0)
      = -(if m = 0 then 0 else g m) := by
    match m with
    | 0 => simp
    | k + 1 =>
      have hcongr : ∀ s ∈ Finset.range n, (if s + 1 = k + 1 then -g (k + 1) else 0)
          = (if s = k then -g (k + 1) else 0) := by
        intro s _
        by_cases h : s = k <;> simp [h]
      rw [Finset.sum_congr rfl hcongr,
        Finset.sum_ite_eq' (Finset.range n) k fun _ ↦ -g (k + 1)]
      have hk : k < n := by omega
      rw [ite_eq_left (Finset.mem_range.2 hk), ite_eq_right (Nat.succ_ne_zero k)]
  rw [h1, h2, h3]
  ring

/-- **The row sums of a type-`A` Cartan matrix.** A row of `CartanMatrix.A n` sums to `2` less the
number of neighbours the position has, so it is `1` at each of the two ends of the chain and `0` in
its interior. This is the constant-weight case of `TauCeti.sum_range_chainEntry_mul`. -/
theorem sum_cartanMatrix_A_row {n : ℕ} (i : Fin n) :
    ∑ j, CartanMatrix.A n i j
      = (if (i : ℕ) = 0 then 1 else 0) + if (i : ℕ) + 1 = n then 1 else 0 := by
  have key := sum_range_chainEntry_mul i.isLt fun _ ↦ (1 : ℚ)
  rw [← Fin.sum_univ_eq_sum_range (fun s ↦ ((chainEntry i s : ℤ) : ℚ) * 1) n] at key
  simp only [mul_one, chainEntry_eq_cartanMatrix_A] at key
  refine Int.cast_injective (α := ℚ) ?_
  push_cast
  rw [key]
  split_ifs <;> norm_num

end TauCeti
