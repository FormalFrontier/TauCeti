/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Ring.NegOnePow
public import TauCeti.GroupTheory.Perm.Inversion
public import TauCeti.KnotTheory.Grid.Diagram.Components
public import TauCeti.KnotTheory.Grid.Grading.Integer

/-!
# Parity of the gradings, and integrality of the Alexander grading

The Maslov gradings of a grid diagram are integers, and the Alexander grading
`A = (M_O - M_X) / 2 - (n - 1) / 2` is a priori only a half-integer. This file computes the parity
of both Maslov gradings and settles the parity-sensitive question: `A` is an integer exactly when
the diagram presents an odd number of link components, in particular whenever it presents a knot.

The mechanism is that `(-1)^{M_O(x)}` is, up to a factor depending only on the diagram, the sign
of the permutation underlying the grid state `x`. Writing `𝕆` for the `O`-marking state,

`M_O(x) = I(x, x) - JNumCentre(x, 𝕆) + I(𝕆, 𝕆) + 1`,

the two self-pairings are the *non-inversion* counts of `x` and of `𝕆`, so modulo two they are the
inversion counts shifted by the common number of column pairs; and the mixed term has the parity
of the grid size, whatever the two permutations are. That last statement is the one piece of real
combinatorics: fibring the mixed count over the columns of `x`, the fibre over `c` contributes
`n - x(c) + c` up to an even correction, and `∑ x(c) = ∑ c` because `x` is a permutation, so the
whole count is `n²` up to an even correction.

Consequently `(-1)^{M_O(x) - M_X(x)}` does not depend on `x` at all: it is the product of the
signs of the two marking permutations, which is the sign of the component permutation
`𝕏⁻¹ ∘ 𝕆`, hence `(-1)^{n + ℓ}` for `ℓ` the number of link components. The normalization shift
`n - 1` then leaves `2 A(x) ≡ ℓ - 1 (mod 2)`.

## Main results

* `TauCeti.GridState.even_JNumCentre_pointSet_add`: the marking-pairing numerator of two grid
  states has the parity of the grid size.
* `TauCeti.GridDiagram.negOnePow_maslovOℤ`, `TauCeti.GridDiagram.negOnePow_maslovXℤ`: the parity
  of a Maslov grading is the sign of the grid state times the sign of the marking permutation.
* `TauCeti.GridDiagram.negOnePow_alexanderTwoℤ`: twice the Alexander grading has the parity of
  the number of link components minus one, for every grid state.
* `TauCeti.GridDiagram.even_alexanderTwoℤ_iff`: the Alexander grading is an integer exactly when
  the number of link components is odd.
* `TauCeti.GridDiagram.alexander_exists_int`: the Alexander grading of a knot grid diagram is an
  integer.

## References

This completes `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.2, "Gradings. The
`J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change formulas across a
rectangle." Integrality of `A` on a knot diagram, and the half-integer shift for an even number
of components, are Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.3.
-/

public section

namespace TauCeti

open Finset

namespace GridState

variable {n : ℕ}

/-- A count of column pairs, fibred over the first column. -/
private theorem card_filter_prod_left (P : Fin n → Fin n → Prop) [DecidableRel P] :
    (Finset.univ.filter fun p : Fin n × Fin n => P p.1 p.2).card =
      ∑ c : Fin n, (Finset.univ.filter fun d : Fin n => P c d).card := by
  simp only [Finset.card_filter]
  exact Fintype.sum_prod_type fun p : Fin n × Fin n => if P p.1 p.2 then 1 else 0

/-- A count of column pairs, fibred over the second column. -/
private theorem card_filter_prod_right (P : Fin n → Fin n → Prop) [DecidableRel P] :
    (Finset.univ.filter fun p : Fin n × Fin n => P p.1 p.2).card =
      ∑ d : Fin n, (Finset.univ.filter fun c : Fin n => P c d).card := by
  simp only [Finset.card_filter]
  exact Fintype.sum_prod_type_right fun p : Fin n × Fin n => if P p.1 p.2 then 1 else 0

/-- The columns whose marking row is at least `k` split into those at or after `c` and those
before `c`. -/
private theorem card_ge_split (y : GridState n) (k c : Fin n) :
    (Finset.univ.filter fun d : Fin n => c ≤ d ∧ k ≤ y d).card
        + (Finset.univ.filter fun d : Fin n => d < c ∧ k ≤ y d).card
      = (Finset.univ.filter fun d : Fin n => k ≤ y d).card := by
  classical
  have e₁ : (Finset.univ.filter fun d : Fin n => k ≤ y d).filter (fun d => c ≤ d) =
      Finset.univ.filter fun d : Fin n => c ≤ d ∧ k ≤ y d := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun d _ => and_comm
  have e₂ : (Finset.univ.filter fun d : Fin n => k ≤ y d).filter (fun d => ¬ c ≤ d) =
      Finset.univ.filter fun d : Fin n => d < c ∧ k ≤ y d := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    rw [not_le]
    exact and_comm
  rw [← e₁, ← e₂]
  exact Finset.card_filter_add_card_filter_not _

/-- There are `n - k` columns whose marking row is at least `k`, because the rows of a grid state
run over every row exactly once. -/
private theorem card_ge_add_val (y : GridState n) (k : Fin n) :
    (Finset.univ.filter fun d : Fin n => k ≤ y d).card + (k : ℕ) = n := by
  classical
  have hcomp : (Finset.univ.filter fun d : Fin n => k ≤ y d).card
      = (Finset.univ.filter fun r : Fin n => k ≤ r).card := by
    simp only [Finset.card_filter]
    exact Equiv.sum_comp y.toPerm fun r : Fin n => if k ≤ r then 1 else 0
  have hIci : (Finset.univ.filter fun r : Fin n => k ≤ r) = Finset.Ici k := by
    ext r
    simp
  have hk := k.isLt
  rw [hcomp, hIci, Fin.card_Ici]
  omega

/-- The columns before `c` split according to whether their marking row lies below the row `x c`
occupied by the grid state. -/
private theorem card_lt_split (x y : GridState n) (c : Fin n) :
    (Finset.univ.filter fun d : Fin n => d < c ∧ y d < x c).card
        + (Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d).card = (c : ℕ) := by
  classical
  have e₁ : (Finset.univ.filter fun d : Fin n => d < c).filter (fun d => y d < x c) =
      Finset.univ.filter fun d : Fin n => d < c ∧ y d < x c :=
    Finset.filter_filter _ _ _
  have e₂ : (Finset.univ.filter fun d : Fin n => d < c).filter (fun d => ¬ y d < x c) =
      Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun d _ => ?_
    rw [not_lt]
  have hIio : (Finset.univ.filter fun d : Fin n => d < c) = Finset.Iio c := by
    ext d
    simp
  rw [← e₁, ← e₂, Finset.card_filter_add_card_filter_not, hIio, Fin.card_Iio]

/-- The marking-pairing numerator of two grid states differs from `n²` by an even amount. Fibring
the count over the columns of the left state, the fibre over `c` contributes `n - x c + c` up to
twice the number of columns before `c` whose right row is at least `x c`, and the two sums
`∑ x c` and `∑ c` agree because a grid state is a permutation. -/
theorem JNumCentre_pointSet_add_two_mul_eq (x y : GridState n) :
    GridPoint.JNumCentre x.pointSet y.pointSet
        + 2 * ∑ c : Fin n, (Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d).card
      = n * n := by
  classical
  have hA : GridPoint.ICentre x.pointSet y.pointSet
      = ∑ c : Fin n, (Finset.univ.filter fun d : Fin n => c ≤ d ∧ x c ≤ y d).card := by
    rw [ICentre_pointSet_eq_card]
    exact card_filter_prod_left fun c d => c ≤ d ∧ x c ≤ y d
  have hB : GridPoint.I y.pointSet x.pointSet
      = ∑ c : Fin n, (Finset.univ.filter fun d : Fin n => d < c ∧ y d < x c).card := by
    rw [I_pointSet_eq_card]
    exact card_filter_prod_right fun d c => d < c ∧ y d < x c
  have key : ∀ c : Fin n,
      (Finset.univ.filter fun d : Fin n => c ≤ d ∧ x c ≤ y d).card
          + (Finset.univ.filter fun d : Fin n => d < c ∧ y d < x c).card
          + 2 * (Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d).card + (x c : ℕ)
        = n + (c : ℕ) := by
    intro c
    have h₃ := card_ge_split y (x c) c
    have h₄ := card_ge_add_val y (x c)
    have h₅ := card_lt_split x y c
    omega
  have hsum : ∑ c : Fin n,
      ((Finset.univ.filter fun d : Fin n => c ≤ d ∧ x c ≤ y d).card
          + (Finset.univ.filter fun d : Fin n => d < c ∧ y d < x c).card
          + 2 * (Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d).card + (x c : ℕ))
      = ∑ _c : Fin n, n + ∑ c : Fin n, (c : ℕ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => key c
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hsum
  have hval : ∑ c : Fin n, ((x c : ℕ)) = ∑ c : Fin n, (c : ℕ) :=
    Equiv.sum_comp x.toPerm fun r : Fin n => (r : ℕ)
  have hconst : ∑ _c : Fin n, n = n * n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [GridPoint.JNumCentre_def, hA, hB]
  omega

/-- The marking-pairing numerator of two grid states has the parity of the grid size. -/
theorem even_JNumCentre_pointSet_add (x y : GridState n) :
    Even ((GridPoint.JNumCentre x.pointSet y.pointSet : ℤ) + n) := by
  have h := JNumCentre_pointSet_add_two_mul_eq x y
  have h' : (GridPoint.JNumCentre x.pointSet y.pointSet : ℤ)
      + 2 * ((∑ c : Fin n,
          (Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d).card : ℕ) : ℤ)
      = (n : ℤ) * n := by exact_mod_cast h
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self (n : ℤ)
  exact ⟨m - ((∑ c : Fin n,
      (Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d).card : ℕ) : ℤ), by nlinarith [hm, h']⟩

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- `(-1)` to a natural power, as the `negOnePow` of the corresponding integer. -/
private theorem neg_one_pow_eq_negOnePow (m : ℕ) : (-1 : ℤˣ) ^ m = ((m : ℕ) : ℤ).negOnePow := by
  rw [Int.negOnePow_def, zpow_natCast]

/-- The parity of the `O`-Maslov grading of a grid state is the sign of the state's permutation,
corrected by the sign of the `O`-marking permutation and by the grid size. In particular the
Maslov grading changes parity under every transposition of two columns of the state. -/
theorem negOnePow_maslovOℤ (x : GridState n) :
    (G.maslovOℤ x).negOnePow =
      Equiv.Perm.sign x.toPerm * Equiv.Perm.sign G.O.toPerm * ((n : ℤ) + 1).negOnePow := by
  classical
  have hx : (GridPoint.I x.pointSet x.pointSet : ℤ)
      + ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.2 < x p.1).card : ℤ)
      = ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card : ℤ) := by
    rw [GridState.I_self_pointSet_eq_card]
    exact_mod_cast GridState.card_filter_noninversion_add_card_filter_inversion x
  have hO : (GridPoint.I G.OSet G.OSet : ℤ)
      + ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.O p.2 < G.O p.1).card : ℤ)
      = ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card : ℤ) := by
    rw [OSet, GridState.I_self_pointSet_eq_card]
    exact_mod_cast GridState.card_filter_noninversion_add_card_filter_inversion G.O
  obtain ⟨k, hk⟩ : Even ((GridPoint.JNumCentre x.pointSet G.OSet : ℤ) + n) := by
    rw [OSet]
    exact GridState.even_JNumCentre_pointSet_add x G.O
  have heq : (G.maslovOℤ x).negOnePow =
      (((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.2 < x p.1).card : ℤ)
        + ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.O p.2 < G.O p.1).card : ℤ)
        + ((n : ℤ) + 1)).negOnePow := by
    refine (Int.negOnePow_eq_iff _ _).mpr ?_
    refine ⟨((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card : ℤ)
      - ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.2 < x p.1).card : ℤ)
      - ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.O p.2 < G.O p.1).card : ℤ)
      - k, ?_⟩
    rw [maslovOℤ_def]
    linarith
  rw [heq, Int.negOnePow_add, Int.negOnePow_add, ← neg_one_pow_eq_negOnePow,
    ← neg_one_pow_eq_negOnePow, ← sign_eq_neg_one_pow_card_inversion,
    ← sign_eq_neg_one_pow_card_inversion]

/-- The parity of the `X`-Maslov grading of a grid state is the sign of the state's permutation,
corrected by the sign of the `X`-marking permutation and by the grid size. -/
theorem negOnePow_maslovXℤ (x : GridState n) :
    (G.maslovXℤ x).negOnePow =
      Equiv.Perm.sign x.toPerm * Equiv.Perm.sign G.X.toPerm * ((n : ℤ) + 1).negOnePow := by
  have h := negOnePow_maslovOℤ G.swapMarkings x
  rwa [maslovOℤ_swapMarkings, swapMarkings_O] at h

/-- The signs of the two marking permutations multiply to the sign of the component permutation,
which is `(-1)` to the grid size plus the number of link components. -/
theorem sign_O_mul_sign_X :
    Equiv.Perm.sign G.O.toPerm * Equiv.Perm.sign G.X.toPerm
      = ((n : ℤ) + G.componentCount).negOnePow := by
  have h := Equiv.Perm.sign_of_cycleType G.componentPerm
  rw [← componentCycleType_def, sum_componentCycleType, ← componentCount_def,
    neg_one_pow_eq_negOnePow, componentPerm_def, map_mul, Equiv.Perm.sign_inv] at h
  rw [mul_comm (Equiv.Perm.sign G.O.toPerm), h]
  norm_cast

/-- Twice the Alexander grading has the parity of the number of link components minus one, for
every grid state: the state-dependent part of the two Maslov parities cancels. -/
theorem negOnePow_alexanderTwoℤ (x : GridState n) :
    (G.alexanderTwoℤ x).negOnePow = ((G.componentCount : ℤ) + 1).negOnePow := by
  have hsplit : (G.alexanderTwoℤ x).negOnePow =
      (G.maslovOℤ x).negOnePow * (G.maslovXℤ x).negOnePow * ((n : ℤ) - 1).negOnePow := by
    rw [alexanderTwoℤ_def, Int.negOnePow_sub, Int.negOnePow_sub]
  have hrearrange :
      Equiv.Perm.sign x.toPerm * Equiv.Perm.sign G.O.toPerm * ((n : ℤ) + 1).negOnePow *
          (Equiv.Perm.sign x.toPerm * Equiv.Perm.sign G.X.toPerm * ((n : ℤ) + 1).negOnePow) *
          ((n : ℤ) - 1).negOnePow
        = Equiv.Perm.sign x.toPerm * Equiv.Perm.sign x.toPerm *
          (((n : ℤ) + 1).negOnePow * ((n : ℤ) + 1).negOnePow) *
          (Equiv.Perm.sign G.O.toPerm * Equiv.Perm.sign G.X.toPerm *
            ((n : ℤ) - 1).negOnePow) := by
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [hsplit, negOnePow_maslovOℤ, negOnePow_maslovXℤ, hrearrange, Int.units_mul_self,
    Int.units_mul_self, one_mul, one_mul, sign_O_mul_sign_X, ← Int.negOnePow_add]
  exact (Int.negOnePow_eq_iff _ _).mpr ⟨(n : ℤ) - 1, by ring⟩

/-- The Alexander grading of a grid state is an integer exactly when the diagram presents an odd
number of link components. -/
theorem even_alexanderTwoℤ_iff (x : GridState n) :
    Even (G.alexanderTwoℤ x) ↔ Odd G.componentCount := by
  rw [← Int.negOnePow_eq_one_iff, negOnePow_alexanderTwoℤ, Int.negOnePow_eq_one_iff,
    Int.even_add_one, Int.not_even_iff_odd, Int.odd_coe_nat]

/-- Twice the Alexander gradings of any two grid states of a fixed diagram differ by an even
integer: the Alexander grading takes all its values in one coset of `ℤ`. -/
theorem even_alexanderTwoℤ_sub (x y : GridState n) :
    Even (G.alexanderTwoℤ x - G.alexanderTwoℤ y) := by
  refine (Int.negOnePow_eq_iff _ _).mp ?_
  rw [negOnePow_alexanderTwoℤ, negOnePow_alexanderTwoℤ]

/-- Twice the Alexander grading of a grid state in a knot diagram is even. -/
theorem even_alexanderTwoℤ_of_isKnot (hG : G.IsKnot) (x : GridState n) :
    Even (G.alexanderTwoℤ x) := by
  have h₁ : G.componentCount = 1 := G.isKnot_def.mp hG
  rw [even_alexanderTwoℤ_iff, h₁]
  exact odd_one

/-- **The Alexander grading of a knot grid diagram is an integer.** This is the parity-sensitive
statement that integrality of the two Maslov gradings stops short of: in general `A` is only a
half-integer, and it is an integer exactly on a diagram with an odd number of components. -/
theorem alexander_exists_int (hG : G.IsKnot) (x : GridState n) :
    ∃ a : ℤ, G.alexander x = (a : ℚ) := by
  obtain ⟨a, ha⟩ := G.even_alexanderTwoℤ_of_isKnot hG x
  refine ⟨a, ?_⟩
  have h := G.two_mul_alexander_eq_intCast x
  rw [ha] at h
  push_cast at h
  linarith

end GridDiagram

end TauCeti
