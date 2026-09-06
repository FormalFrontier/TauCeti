/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Choose.Sum
public import TauCeti.Combinatorics.Young.DualPieri
public import TauCeti.Combinatorics.Young.Interlacing
public import TauCeti.Combinatorics.Young.StandardTableau.Reading

/-!
# The dimension count behind Schur–Weyl duality

Schur–Weyl duality decomposes the `n`-th tensor power of `ℂ^d` as a representation of
`Sₙ × GL_d`:

`(ℂ^d)^{⊗ n} ≅ ⊕_{λ ⊢ n} S^λ ⊗ 𝕊^λ(ℂ^d)`.

Taking dimensions turns this into a purely combinatorial identity, since `dim S^λ` is the number
of standard Young tableaux of shape `λ` and `dim 𝕊^λ(ℂ^d)` is the number of semistandard Young
tableaux of shape `λ` with entries among `d` letters:

`∑_{λ ⊢ n} f^λ · K_d(λ) = d ^ n`.

This file proves that identity, `TauCeti.sum_standardCount_mul_card_boundedSSYT`.  No condition
`ℓ(λ) ≤ d` is needed: a shape with more than `d` rows admits no semistandard tableau in `d`
letters (`TauCeti.BoundedSSYT.isEmpty_of_lt_colLen`), so its term vanishes on its own.

The proof is an induction on the number `d` of letters.  The branching rule
`TauCeti.BoundedSSYT.card_eq_sum_interlacingShapes` writes `K_{d+1}(μ)` as the sum of `K_d(ν)`
over the shapes `ν` interlacing `μ`; exchanging the two summations and applying the dual Pieri
rule `TauCeti.sum_standardCount_interlacedBy` to the inner sum turns the total into

`∑_{k ≤ n} C(n, k) · ∑_{ν ⊢ k} f^ν · K_d(ν) = ∑_{k ≤ n} C(n, k) · d ^ k = (d + 1) ^ n`

by the inductive hypothesis and the binomial theorem.

## Main results

* `TauCeti.sum_standardCount_mul_card_boundedSSYT`: the dimension count
  `∑_{λ ⊢ n} f^λ · K_d(λ) = d ^ n`.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 8.1.
* [R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*][goodman2009],
  Chapter 9.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 8: Schur-Weyl duality
-/

public section

namespace YoungDiagram

/-- A shape with at least one cell has at least one row. -/
theorem colLen_zero_pos_of_card_pos {μ : _root_.YoungDiagram} (h : 0 < μ.card) :
    0 < μ.colLen 0 := by
  obtain ⟨c, hc⟩ := Finset.card_pos.mp h
  have h00 : (0, 0) ∈ μ := μ.up_left_mem (Nat.zero_le _) (Nat.zero_le _) hc
  exact _root_.YoungDiagram.mem_iff_lt_colLen.mp h00

/-- Interlacing shapes are smaller. -/
theorem InterlacedBy.card_le {μ ν : _root_.YoungDiagram} (h : InterlacedBy μ ν) :
    ν.card ≤ μ.card :=
  Finset.card_le_card h.le

end YoungDiagram

open YoungDiagram

namespace TauCeti

/-- There are no semistandard tableaux with `d` letters on a shape with more than `d` rows, so
such shapes may be added freely to a sum of tableau counts. -/
theorem BoundedSSYT.card_eq_zero_of_lt_colLen {d : ℕ} {ν : YoungDiagram} (h : d < ν.colLen 0) :
    Fintype.card (BoundedSSYT d ν) = 0 :=
  have := BoundedSSYT.isEmpty_of_lt_colLen h
  Fintype.card_eq_zero

/-- The branching rule, restated as a sum over all shapes with at most `n` cells: the summands
indexed by shapes that do not interlace `μ`, or that have too many rows, vanish. -/
theorem BoundedSSYT.card_succ_eq_sum_shapesOfSizeLE (d n : ℕ) {μ : YoungDiagram}
    (hμ : μ.card = n) :
    Fintype.card (BoundedSSYT (d + 1) μ)
      = ∑ ν ∈ shapesOfSizeLE n,
          if InterlacedBy μ ν then Fintype.card (BoundedSSYT d ν) else 0 := by
  rw [BoundedSSYT.card_eq_sum_interlacingShapes, ← Finset.sum_filter]
  refine Finset.sum_subset (fun ν hν => ?_) fun ν hν hνnot => ?_
  · rw [YoungDiagram.mem_interlacingShapes] at hν
    rw [Finset.mem_filter, mem_shapesOfSizeLE]
    exact ⟨hμ ▸ hν.1.card_le, hν.1⟩
  · rw [Finset.mem_filter] at hν
    rw [YoungDiagram.mem_interlacingShapes] at hνnot
    refine BoundedSSYT.card_eq_zero_of_lt_colLen ?_
    by_contra hle
    exact hνnot ⟨hν.2, by omega⟩

/-- **The Schur–Weyl dimension count**: summing over the shapes with `n` cells, the number of
standard Young tableaux times the number of semistandard Young tableaux with entries below `d`
gives `d ^ n`.  This is the numerical shadow of `(ℂ^d)^{⊗ n} ≅ ⊕_λ S^λ ⊗ 𝕊^λ(ℂ^d)`. -/
theorem sum_standardCount_mul_card_boundedSSYT (d n : ℕ) :
    ∑ μ ∈ shapesOfSize n, standardCount μ * Fintype.card (BoundedSSYT d μ) = d ^ n := by
  induction d generalizing n with
  | zero =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [shapesOfSize_zero, Finset.sum_singleton,
        standardCount_eq_one_of_rowLen_le_one (by simp), Fintype.card_unique, pow_zero, one_mul]
    · refine (Finset.sum_eq_zero fun μ hμ => ?_).trans (zero_pow hn.ne').symm
      have hcard : μ.card = n := mem_shapesOfSize.mp hμ
      rw [BoundedSSYT.card_eq_zero_of_lt_colLen
        (YoungDiagram.colLen_zero_pos_of_card_pos (by omega)), mul_zero]
  | succ d ih =>
    have hbranch : ∀ μ ∈ shapesOfSize n,
        standardCount μ * Fintype.card (BoundedSSYT (d + 1) μ)
          = ∑ ν ∈ shapesOfSizeLE n,
              if InterlacedBy μ ν then standardCount μ * Fintype.card (BoundedSSYT d ν) else 0 := by
      intro μ hμ
      rw [BoundedSSYT.card_succ_eq_sum_shapesOfSizeLE d n (mem_shapesOfSize.mp hμ),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun ν _ => by split_ifs <;> simp
    rw [Finset.sum_congr rfl hbranch, Finset.sum_comm]
    have hinner : ∀ ν ∈ shapesOfSizeLE n,
        ∑ μ ∈ shapesOfSize n,
            (if InterlacedBy μ ν then standardCount μ * Fintype.card (BoundedSSYT d ν) else 0)
          = n.choose ν.card * (standardCount ν * Fintype.card (BoundedSSYT d ν)) := by
      intro ν _
      rw [← Finset.sum_filter (p := fun μ => InterlacedBy μ ν), ← Finset.sum_mul,
        sum_standardCount_interlacedBy n ν]
      ring
    rw [Finset.sum_congr rfl hinner, sum_shapesOfSizeLE]
    have houter : ∀ k ∈ Finset.range (n + 1),
        ∑ ν ∈ shapesOfSize k, n.choose ν.card * (standardCount ν * Fintype.card (BoundedSSYT d ν))
          = n.choose k * d ^ k := by
      intro k _
      rw [← ih k, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ν hν => by rw [mem_shapesOfSize.mp hν]
    rw [Finset.sum_congr rfl houter, add_pow]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_comm]

end TauCeti
