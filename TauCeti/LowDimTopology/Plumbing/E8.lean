/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public import TauCeti.LowDimTopology.Plumbing.NegativeDefinite

/-!
# The negative-definite E₈ plumbing

This file defines the `E₈` plumbing used as the first concrete calculation in the lattice-homology
lane. Its eight vertices all have framing `-2`; vertices `0, ..., 6` form a chain and vertex `7`
is attached to vertex `2`. Thus the negative of its intersection matrix is the `E₈` Cartan
matrix.

The proof of negative-definiteness gives an explicit integral completion of squares. This both
certifies the plumbing without appealing to a classification theorem and records a formula useful
for checking later computations on this example.

## Main definitions

* `TauCeti.e8Plumbing`: the `-2`-framed plumbing on the `E₈` Dynkin tree.

## Main results

* `TauCeti.e8Plumbing_adj`: the seven edges of the plumbing.
* `TauCeti.e8Plumbing_neg_intersectionForm`: the completed-square identity for the negative
  intersection form.
* `TauCeti.e8Plumbing_isNegativeDefinite`: the `E₈` plumbing is negative definite.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L, and specifically its
acceptance check asking that lattice homology be computed for the negative-definite `E₈` plumbing
of the Poincaré sphere. The plumbing convention follows Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 2.
-/

public section

namespace TauCeti

/-- The oriented edge list used to present the `E₈` Dynkin tree. -/
private def e8Edge (i j : Fin 8) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨
    (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 6) ∨
      (i = 2 ∧ j = 7)

private instance : DecidableRel e8Edge := fun _ _ => by
  unfold e8Edge
  infer_instance

/-- The `E₈` plumbing: a chain of seven `-2`-framed vertices, with one further `-2`-framed
vertex attached to the third vertex of the chain. -/
def e8Plumbing : PlumbingGraph (Fin 8) where
  toSimpleGraph := SimpleGraph.fromRel e8Edge
  decidableAdj := inferInstance
  weight := fun _ => -2

/-- Two vertices of the `E₈` plumbing are adjacent exactly when they are one of the seven
unordered pairs in its Dynkin tree. -/
@[simp]
theorem e8Plumbing_adj (i j : Fin 8) :
    e8Plumbing.toSimpleGraph.Adj i j ↔
      ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) ∨
      ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) ∨
      ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) ∨
      ((i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3)) ∨
      ((i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4)) ∨
      ((i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5)) ∨
        ((i = 2 ∧ j = 7) ∨ (i = 7 ∧ j = 2)) := by
  fin_cases i <;> fin_cases j <;>
    simp [e8Plumbing, e8Edge, SimpleGraph.fromRel_adj]

/-- The self-intersection of a vector in the `E₈` plumbing lattice, expanded along the seven
edges of the Dynkin tree. -/
theorem e8Plumbing_intersectionForm_self (x : Fin 8 → ℤ) :
    e8Plumbing.intersectionForm x x =
      -2 * ∑ i, x i ^ 2 +
        2 * (x 0 * x 1 + x 1 * x 2 + x 2 * x 3 + x 3 * x 4 +
          x 4 * x 5 + x 5 * x 6 + x 2 * x 7) := by
  rw [e8Plumbing.intersectionForm_self]
  simp only [Fin.sum_univ_eight]
  simp [e8Plumbing, e8Edge]
  ring

/-- The eight nonnegative square terms in the integral completion of squares for the `E₈`
intersection form. -/
def e8SquareTerm (x : Fin 8 → ℤ) : Fin 8 → ℤ :=
  ![420 * (2 * x 0 - x 1) ^ 2,
    140 * (3 * x 1 - 2 * x 2) ^ 2,
    70 * (4 * x 2 - 3 * x 3 - 3 * x 7) ^ 2,
    42 * (5 * x 3 - 4 * x 4 - 3 * x 7) ^ 2,
    28 * (6 * x 4 - 5 * x 5 - 3 * x 7) ^ 2,
    20 * (7 * x 5 - 6 * x 6 - 3 * x 7) ^ 2,
    15 * (8 * x 6 - 3 * x 7) ^ 2,
    105 * x 7 ^ 2]

/-- The zeroth completed-square term. -/
@[simp] theorem e8SquareTerm_zero (x : Fin 8 → ℤ) :
    e8SquareTerm x 0 = 420 * (2 * x 0 - x 1) ^ 2 := (rfl)

/-- The first completed-square term. -/
@[simp] theorem e8SquareTerm_one (x : Fin 8 → ℤ) :
    e8SquareTerm x 1 = 140 * (3 * x 1 - 2 * x 2) ^ 2 := (rfl)

/-- The second completed-square term. -/
@[simp] theorem e8SquareTerm_two (x : Fin 8 → ℤ) :
    e8SquareTerm x 2 = 70 * (4 * x 2 - 3 * x 3 - 3 * x 7) ^ 2 := (rfl)

/-- The third completed-square term. -/
@[simp] theorem e8SquareTerm_three (x : Fin 8 → ℤ) :
    e8SquareTerm x 3 = 42 * (5 * x 3 - 4 * x 4 - 3 * x 7) ^ 2 := (rfl)

/-- The fourth completed-square term. -/
@[simp] theorem e8SquareTerm_four (x : Fin 8 → ℤ) :
    e8SquareTerm x 4 = 28 * (6 * x 4 - 5 * x 5 - 3 * x 7) ^ 2 := (rfl)

/-- The fifth completed-square term. -/
@[simp] theorem e8SquareTerm_five (x : Fin 8 → ℤ) :
    e8SquareTerm x 5 = 20 * (7 * x 5 - 6 * x 6 - 3 * x 7) ^ 2 := (rfl)

/-- The sixth completed-square term. -/
@[simp] theorem e8SquareTerm_six (x : Fin 8 → ℤ) :
    e8SquareTerm x 6 = 15 * (8 * x 6 - 3 * x 7) ^ 2 := (rfl)

/-- The seventh completed-square term. -/
@[simp] theorem e8SquareTerm_seven (x : Fin 8 → ℤ) :
    e8SquareTerm x 7 = 105 * x 7 ^ 2 := (rfl)

/-- Every term in the completed-square expression for `E₈` is nonnegative. -/
theorem e8SquareTerm_nonneg (x : Fin 8 → ℤ) (i : Fin 8) : 0 ≤ e8SquareTerm x i := by
  fin_cases i <;> exact mul_nonneg (by norm_num) (sq_nonneg _)

/-- An integral completion of squares for the negative `E₈` intersection form. Multiplication by
`840` clears the denominators in the usual `LDLᵀ` decomposition of the `E₈` Cartan matrix. -/
theorem e8Plumbing_neg_intersectionForm (x : Fin 8 → ℤ) :
    -840 * e8Plumbing.intersectionForm x x = ∑ i, e8SquareTerm x i := by
  rw [e8Plumbing_intersectionForm_self]
  simp only [Fin.sum_univ_eight]
  simp [e8SquareTerm]
  ring

/-- The `E₈` plumbing is negative definite. -/
theorem e8Plumbing_isNegativeDefinite : e8Plumbing.IsNegativeDefinite := by
  rw [PlumbingGraph.isNegativeDefinite_iff_forall_intersectionForm_self_neg]
  intro x hx
  have hid := e8Plumbing_neg_intersectionForm x
  by_contra hneg
  have hform : 0 ≤ e8Plumbing.intersectionForm x x := le_of_not_gt hneg
  have hR : ∑ i, e8SquareTerm x i = 0 := by
    have : 0 ≤ ∑ i, e8SquareTerm x i :=
      Finset.sum_nonneg fun i _ => e8SquareTerm_nonneg x i
    nlinarith
  have hterm (i : Fin 8) : e8SquareTerm x i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => e8SquareTerm_nonneg x j).mp hR i
      (Finset.mem_univ i)
  have hz7 : x 7 = 0 := by
    have := hterm 7
    rw [e8SquareTerm_seven] at this
    nlinarith [sq_nonneg (x 7)]
  have hz6 : x 6 = 0 := by
    have this := hterm 6
    rw [e8SquareTerm_six] at this
    rw [hz7] at this
    nlinarith [sq_nonneg (x 6)]
  have hz5 : x 5 = 0 := by
    have this := hterm 5
    rw [e8SquareTerm_five] at this
    rw [hz6, hz7] at this
    nlinarith [sq_nonneg (x 5)]
  have hz4 : x 4 = 0 := by
    have hs := hterm 4
    rw [e8SquareTerm_four] at hs
    rw [hz5, hz7] at hs
    nlinarith [sq_nonneg (x 4)]
  have hz3 : x 3 = 0 := by
    have hs := hterm 3
    rw [e8SquareTerm_three] at hs
    rw [hz4, hz7] at hs
    nlinarith [sq_nonneg (x 3)]
  have hz2 : x 2 = 0 := by
    have hs := hterm 2
    rw [e8SquareTerm_two] at hs
    rw [hz3, hz7] at hs
    nlinarith [sq_nonneg (x 2)]
  have hz1 : x 1 = 0 := by
    have hs := hterm 1
    rw [e8SquareTerm_one] at hs
    rw [hz2] at hs
    nlinarith [sq_nonneg (x 1)]
  have hz0 : x 0 = 0 := by
    have hs := hterm 0
    rw [e8SquareTerm_zero] at hs
    rw [hz1] at hs
    nlinarith [sq_nonneg (x 0)]
  apply hx
  funext i
  fin_cases i <;> assumption

end TauCeti
