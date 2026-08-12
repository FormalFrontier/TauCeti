/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan

public section

/-!
# Chains of simple edges

The diagrams that the classification of finite-type Cartan matrices has to weigh are built out of
**chains**: runs of vertices joined by single edges. This file isolates the entry function of such
a run, `TauCeti.chainEntry`, together with the one summation identity that every weighting argument
along a chain needs, `TauCeti.sum_range_chainEntry_mul`: the row of a chain at a position collects
the second difference of the weight there.

Nothing here mentions `TauCeti.IsFiniteType`, which is why the file sits above the finite-type
directory rather than in it. It exists because the diagrams that carry the two length constraints
of the classification - the stars of
`TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Basic` and the double-edge chains of
`TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Basic` - are both assembled from chains and
are both excluded by a vector that is linear along each of them.

## Main definitions

* `TauCeti.chainEntry`: the Cartan-matrix entry of a chain between two positions along it.

## Main results

* `TauCeti.chainEntry_eq_cartanMatrix_A`: a chain of `n` positions is Mathlib's Cartan matrix of
  type `Aₙ`, which is what makes the name of the entry function the right one.
* `TauCeti.sum_range_chainEntry_mul`: the row of a chain at a position, evaluated at a weight `g`.
  Away from the two ends it is the second difference `2 g (m + 1) - g m - g (m + 2)`, so a weight
  that is linear in the position is annihilated there.
## References

The chain weighting is the calculation of J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, §11.4, and Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §4.
-/

namespace TauCeti

/-- The Cartan-matrix entry of a **chain** between the positions `s` and `t` along it: `2` on the
diagonal, `-1` between consecutive positions, and `0` otherwise. A chain is simply laced, so this
single function describes all of its edges. -/
def chainEntry (s t : ℕ) : ℤ :=
  if s = t then 2 else if s = t + 1 then -1 else if t = s + 1 then -1 else 0

-- `(rfl)`, not `rfl`: the body of `TauCeti.chainEntry` is deliberately left unexposed, and the
-- parenthesised form keeps this equation out of the exported definitional-equality check.
lemma chainEntry_def (s t : ℕ) :
    chainEntry s t = if s = t then 2 else if s = t + 1 then -1 else if t = s + 1 then -1 else 0 :=
  (rfl)

@[simp] lemma chainEntry_self (s : ℕ) : chainEntry s s = 2 := by simp [chainEntry]

@[simp] lemma chainEntry_succ_left (s : ℕ) : chainEntry (s + 1) s = -1 := by
  unfold chainEntry; split_ifs <;> omega

@[simp] lemma chainEntry_succ_right (s : ℕ) : chainEntry s (s + 1) = -1 := by
  unfold chainEntry; split_ifs <;> omega

/-- Away from the diagonal and its two neighbours a chain has no entry. -/
@[simp] lemma chainEntry_eq_zero {s t : ℕ} (h1 : s ≠ t) (h2 : s ≠ t + 1) (h3 : t ≠ s + 1) :
    chainEntry s t = 0 := by
  unfold chainEntry; split_ifs <;> omega

/-- Shifting both positions of a chain by one leaves the entry unchanged: only the difference of
the positions matters. This is not a `simp` lemma: it would rewrite the right-hand sides of the
entry lemmas for `TauCeti.starCartanMatrix`, whose arm positions are shifted by one against the
centre, out of the form those lemmas state. -/
lemma chainEntry_succ_succ (s t : ℕ) : chainEntry (s + 1) (t + 1) = chainEntry s t := by
  unfold chainEntry; split_ifs <;> omega

/-- A chain is symmetric: the entry depends on the unordered pair of positions. -/
lemma chainEntry_comm (s t : ℕ) : chainEntry s t = chainEntry t s := by
  unfold chainEntry; split_ifs <;> omega

/-- A chain is Mathlib's Cartan matrix of type `A`: on `n` positions the two entry rules agree. -/
lemma chainEntry_eq_cartanMatrix_A {n : ℕ} (i j : Fin n) :
    chainEntry i j = CartanMatrix.A n i j := by
  simp only [chainEntry, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
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
  have key : ∀ s ∈ Finset.range n, ((chainEntry m s : ℤ) : R) * g (s + 1)
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
  abel

end TauCeti
