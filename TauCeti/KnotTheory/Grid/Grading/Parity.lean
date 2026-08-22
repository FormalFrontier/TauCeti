/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Ring.NegOnePow
import TauCeti.GroupTheory.Perm.Inversion
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

`M_O(x) = I(x, x) - JNumCenter(x, 𝕆) + I(𝕆, 𝕆) + 1`,

the two self-pairings are the non-inversion counts of `x` and of `𝕆`, while the mixed term has the
parity of the grid size. Fibring the mixed count over the columns of `x`, the fibre over `c`
contributes `n - x(c) + c` up to an even correction. The sums `∑ x(c)` and `∑ c` agree because
`x` is a permutation, so the whole count is `n²` up to an even correction.

Consequently `(-1)^{M_O(x) - M_X(x)}` is independent of `x`: it is the product of the signs of
the two marking permutations, hence the sign of the component permutation `𝕏⁻¹ ∘ 𝕆`, and equals
`(-1)^{n + ℓ}` for `ℓ` link components. The normalization shift `n - 1` leaves
`2 A(x) ≡ ℓ - 1 (mod 2)`.

## Main results

* `TauCeti.GridState.even_JNumCenter_pointSet_add`: the marking-pairing numerator of two grid
  states has the parity of the grid size.
* `TauCeti.GridDiagram.negOnePow_maslovOℤ`, `TauCeti.GridDiagram.negOnePow_maslovXℤ`: the parity
  of a Maslov grading is the sign of the state times the sign of the marking permutation,
  corrected by the grid-size factor `((n : ℤ) + 1).negOnePow`.
* `TauCeti.GridDiagram.negOnePow_alexanderTwoℤ`: twice the Alexander grading has the parity of
  the number of link components minus one.
* `TauCeti.GridDiagram.even_alexanderTwoℤ_iff`: the Alexander grading is an integer exactly when
  the number of link components is odd.
* `TauCeti.GridDiagram.alexander_exists_int_iff`: the direct integrality characterization.
* `TauCeti.GridDiagram.alexander_exists_int_of_isKnot`: the Alexander grading of a knot grid is
  an integer.

## References

This completes the integer-valuedness and parity portion of
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.2; the rectangle marking-count
formulas are separate. Integrality of `A` on a knot diagram, and the half-integer shift for an
even number of components, are from Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 4.3. The Lean proof is adapted to current `main` from the earlier Tau Ceti split-branch
commit `05c2722248`.
-/

public section

namespace TauCeti

open Finset

namespace GridState

variable {n : ℕ}

/-- The columns whose marking row is at least `k` split into those at or after `c` and those
before `c`. -/
private theorem card_ge_split (y : GridState n) (k c : Fin n) :
    (Finset.univ.filter fun d : Fin n => c ≤ d ∧ k ≤ y d).card
        + (Finset.univ.filter fun d : Fin n => d < c ∧ k ≤ y d).card =
      (Finset.univ.filter fun d : Fin n => k ≤ y d).card := by
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
  have hcomp : (Finset.univ.filter fun d : Fin n => k ≤ y d).card =
      (Finset.univ.filter fun r : Fin n => k ≤ r).card := by
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

/-- The marking-pairing numerator of two grid states differs from `n²` by an even amount. -/
private theorem JNumCenter_pointSet_add_two_mul_eq (x y : GridState n) :
    GridPoint.JNumCenter x.pointSet y.pointSet
        + 2 * ∑ c : Fin n,
          (Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d).card =
      n * n := by
  classical
  have hA : GridPoint.ICenter x.pointSet y.pointSet =
      ∑ c : Fin n, (Finset.univ.filter fun d : Fin n => c ≤ d ∧ x c ≤ y d).card := by
    rw [ICenter_pointSet_eq_card]
    symm
    calc
      ∑ c : Fin n, (Finset.univ.filter fun d : Fin n => c ≤ d ∧ x c ≤ y d).card =
          ∑ c ∈ Finset.univ, ((Finset.univ.filter fun p : Fin n × Fin n =>
            p.1 ≤ p.2 ∧ x p.1 ≤ y p.2).filter fun p => Prod.fst p = c).card := by
        apply Finset.sum_congr rfl
        intro c _
        have hfiber :
            ((Finset.univ.filter fun p : Fin n × Fin n =>
              p.1 ≤ p.2 ∧ x p.1 ≤ y p.2).filter fun p => Prod.fst p = c) =
              {c} ×ˢ (Finset.univ.filter fun d : Fin n => c ≤ d ∧ x c ≤ y d) := by
          ext p
          rcases p with ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
            Finset.mem_singleton]
          aesop
        rw [hfiber, Finset.card_product]
        simp
      _ = ((Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 ≤ p.2 ∧ x p.1 ≤ y p.2).filter fun p => Prod.fst p ∈ Finset.univ).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ Prod.fst
      _ = (Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 ≤ p.2 ∧ x p.1 ≤ y p.2).card := by simp
  have hB : GridPoint.I y.pointSet x.pointSet =
      ∑ c : Fin n, (Finset.univ.filter fun d : Fin n => d < c ∧ y d < x c).card := by
    rw [I_pointSet_eq_card]
    symm
    calc
      ∑ c : Fin n, (Finset.univ.filter fun d : Fin n => d < c ∧ y d < x c).card =
          ∑ c ∈ Finset.univ, ((Finset.univ.filter fun p : Fin n × Fin n =>
            p.1 < p.2 ∧ y p.1 < x p.2).filter fun p => Prod.snd p = c).card := by
        apply Finset.sum_congr rfl
        intro c _
        have hfiber :
            ((Finset.univ.filter fun p : Fin n × Fin n =>
              p.1 < p.2 ∧ y p.1 < x p.2).filter fun p => Prod.snd p = c) =
              (Finset.univ.filter fun d : Fin n => d < c ∧ y d < x c) ×ˢ {c} := by
          ext p
          rcases p with ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
            Finset.mem_singleton]
          aesop
        rw [hfiber, Finset.card_product]
        simp
      _ = ((Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 < p.2 ∧ y p.1 < x p.2).filter fun p => Prod.snd p ∈ Finset.univ).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ Prod.snd
      _ = (Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 < p.2 ∧ y p.1 < x p.2).card := by simp
  have key : ∀ c : Fin n,
      (Finset.univ.filter fun d : Fin n => c ≤ d ∧ x c ≤ y d).card
          + (Finset.univ.filter fun d : Fin n => d < c ∧ y d < x c).card
          + 2 * (Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d).card + (x c : ℕ) =
        n + (c : ℕ) := by
    intro c
    have h₃ := card_ge_split y (x c) c
    have h₄ := card_ge_add_val y (x c)
    have h₅ := card_lt_split x y c
    omega
  have hsum : ∑ c : Fin n,
      ((Finset.univ.filter fun d : Fin n => c ≤ d ∧ x c ≤ y d).card
          + (Finset.univ.filter fun d : Fin n => d < c ∧ y d < x c).card
          + 2 * (Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d).card + (x c : ℕ)) =
      ∑ _c : Fin n, n + ∑ c : Fin n, (c : ℕ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => key c
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hsum
  have hval : ∑ c : Fin n, (x c : ℕ) = ∑ c : Fin n, (c : ℕ) :=
    Equiv.sum_comp x.toPerm fun r : Fin n => (r : ℕ)
  have hconst : ∑ _c : Fin n, n = n * n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [GridPoint.JNumCenter_def, hA, hB]
  omega

/-- The marking-pairing numerator of two grid states has the parity of the grid size. -/
theorem even_JNumCenter_pointSet_add (x y : GridState n) :
    Even ((GridPoint.JNumCenter x.pointSet y.pointSet : ℤ) + n) := by
  have h := JNumCenter_pointSet_add_two_mul_eq x y
  have h' : (GridPoint.JNumCenter x.pointSet y.pointSet : ℤ)
      + 2 * ((∑ c : Fin n,
          (Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d).card : ℕ) : ℤ) =
      (n : ℤ) * n := by
    exact_mod_cast h
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self (n : ℤ)
  exact ⟨m - ((∑ c : Fin n,
      (Finset.univ.filter fun d : Fin n => d < c ∧ x c ≤ y d).card : ℕ) : ℤ), by
    nlinarith [hm, h']⟩

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- `(-1)` to a natural power, as the `negOnePow` of the corresponding integer. -/
private theorem neg_one_pow_eq_negOnePow (m : ℕ) :
    (-1 : ℤˣ) ^ m = ((m : ℕ) : ℤ).negOnePow := by
  rw [Int.negOnePow_def, zpow_natCast]

/-- The parity of the `O`-Maslov grading is the sign of the state permutation, corrected by the
sign of the `O`-marking permutation and by the grid size. -/
theorem negOnePow_maslovOℤ (x : GridState n) :
    (G.maslovOℤ x).negOnePow =
      Equiv.Perm.sign x.toPerm * Equiv.Perm.sign G.O.toPerm * ((n : ℤ) + 1).negOnePow := by
  classical
  have hx : (GridPoint.I x.pointSet x.pointSet : ℤ)
      + ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.2 < x p.1).card : ℤ) =
      ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card : ℤ) := by
    rw [GridState.I_self_pointSet_eq_card]
    exact_mod_cast GridState.card_filter_noninversion_add_card_filter_inversion x
  have hO : (GridPoint.I G.OSet G.OSet : ℤ)
      + ((Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ G.O p.2 < G.O p.1).card : ℤ) =
      ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card : ℤ) := by
    rw [OSet, GridState.I_self_pointSet_eq_card]
    exact_mod_cast GridState.card_filter_noninversion_add_card_filter_inversion G.O
  obtain ⟨k, hk⟩ : Even ((GridPoint.JNumCenter x.pointSet G.OSet : ℤ) + n) := by
    rw [OSet]
    exact GridState.even_JNumCenter_pointSet_add x G.O
  have heq : (G.maslovOℤ x).negOnePow =
      (((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.2 < x p.1).card : ℤ)
        + ((Finset.univ.filter fun p : Fin n × Fin n =>
          p.1 < p.2 ∧ G.O p.2 < G.O p.1).card : ℤ)
        + ((n : ℤ) + 1)).negOnePow := by
    refine (Int.negOnePow_eq_iff _ _).mpr ?_
    refine ⟨((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card : ℤ)
      - ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.2 < x p.1).card : ℤ)
      - ((Finset.univ.filter fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ G.O p.2 < G.O p.1).card : ℤ) - k, ?_⟩
    rw [maslovOℤ_def]
    linarith
  rw [heq, Int.negOnePow_add, Int.negOnePow_add, ← neg_one_pow_eq_negOnePow,
    ← neg_one_pow_eq_negOnePow, ← sign_eq_neg_one_pow_card_inversion,
    ← sign_eq_neg_one_pow_card_inversion]

/-- The parity of the `X`-Maslov grading is the analogous expression using the `X` markings. -/
theorem negOnePow_maslovXℤ (x : GridState n) :
    (G.maslovXℤ x).negOnePow =
      Equiv.Perm.sign x.toPerm * Equiv.Perm.sign G.X.toPerm * ((n : ℤ) + 1).negOnePow := by
  have h := negOnePow_maslovOℤ G.swapMarkings x
  rwa [maslovOℤ_swapMarkings, swapMarkings_O] at h

/-- The signs of the marking permutations multiply to the sign of the component permutation,
which is `(-1)` to the grid size plus the number of link components. -/
theorem sign_O_mul_sign_X :
    Equiv.Perm.sign G.O.toPerm * Equiv.Perm.sign G.X.toPerm =
      ((n : ℤ) + G.componentCount).negOnePow := by
  have h := Equiv.Perm.sign_of_cycleType G.componentPerm
  rw [← componentCycleType_def, sum_componentCycleType, ← componentCount_def,
    neg_one_pow_eq_negOnePow, componentPerm_def, map_mul, Equiv.Perm.sign_inv] at h
  rw [mul_comm (Equiv.Perm.sign G.O.toPerm), h]
  norm_cast

/-- Twice the Alexander grading has the parity of the number of link components minus one. -/
theorem negOnePow_alexanderTwoℤ (x : GridState n) :
    (G.alexanderTwoℤ x).negOnePow = ((G.componentCount : ℤ) + 1).negOnePow := by
  have hsplit : (G.alexanderTwoℤ x).negOnePow =
      (G.maslovOℤ x).negOnePow * (G.maslovXℤ x).negOnePow *
        ((n : ℤ) - 1).negOnePow := by
    rw [alexanderTwoℤ_def, Int.negOnePow_sub, Int.negOnePow_sub]
  have hrearrange :
      Equiv.Perm.sign x.toPerm * Equiv.Perm.sign G.O.toPerm * ((n : ℤ) + 1).negOnePow *
          (Equiv.Perm.sign x.toPerm * Equiv.Perm.sign G.X.toPerm * ((n : ℤ) + 1).negOnePow) *
          ((n : ℤ) - 1).negOnePow =
        Equiv.Perm.sign x.toPerm * Equiv.Perm.sign x.toPerm *
          (((n : ℤ) + 1).negOnePow * ((n : ℤ) + 1).negOnePow) *
          (Equiv.Perm.sign G.O.toPerm * Equiv.Perm.sign G.X.toPerm *
            ((n : ℤ) - 1).negOnePow) := by
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [hsplit, negOnePow_maslovOℤ, negOnePow_maslovXℤ, hrearrange, Int.units_mul_self,
    Int.units_mul_self, one_mul, one_mul, sign_O_mul_sign_X, ← Int.negOnePow_add]
  exact (Int.negOnePow_eq_iff _ _).mpr ⟨(n : ℤ) - 1, by ring⟩

/-- The Alexander grading is integral exactly when the diagram has an odd number of components. -/
theorem even_alexanderTwoℤ_iff (x : GridState n) :
    Even (G.alexanderTwoℤ x) ↔ Odd G.componentCount := by
  rw [← Int.negOnePow_eq_one_iff, negOnePow_alexanderTwoℤ, Int.negOnePow_eq_one_iff,
    Int.even_add_one, Int.not_even_iff_odd, Int.odd_coe_nat]

/-- The Alexander grading of a state is an integer exactly when the diagram has an odd number of
link components. For an even number of components, every Alexander grading is a strict
half-integer. -/
theorem alexander_exists_int_iff (x : GridState n) :
    (∃ a : ℤ, G.alexander x = (a : ℚ)) ↔ Odd G.componentCount := by
  rw [← G.even_alexanderTwoℤ_iff x]
  constructor
  · rintro ⟨a, ha⟩
    have h := G.two_mul_alexander_eq_intCast x
    rw [ha] at h
    have h' : G.alexanderTwoℤ x = 2 * a := by
      exact_mod_cast h.symm
    exact ⟨a, by omega⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h := G.two_mul_alexander_eq_intCast x
    rw [ha] at h
    push_cast at h
    linarith

/-- Twice the Alexander gradings of two states differ by an even integer. -/
theorem even_alexanderTwoℤ_sub (x y : GridState n) :
    Even (G.alexanderTwoℤ x - G.alexanderTwoℤ y) := by
  refine (Int.negOnePow_eq_iff _ _).mp ?_
  rw [negOnePow_alexanderTwoℤ, negOnePow_alexanderTwoℤ]

/-- Twice the Alexander grading of a state in a knot grid is even. -/
theorem even_alexanderTwoℤ_of_isKnot (hG : G.IsKnot) (x : GridState n) :
    Even (G.alexanderTwoℤ x) := by
  have h₁ : G.componentCount = 1 := G.isKnot_def.mp hG
  rw [even_alexanderTwoℤ_iff, h₁]
  exact odd_one

/-- **The Alexander grading of a knot grid diagram is an integer.** -/
theorem alexander_exists_int_of_isKnot (hG : G.IsKnot) (x : GridState n) :
    ∃ a : ℤ, G.alexander x = (a : ℚ) := by
  rw [G.alexander_exists_int_iff]
  rw [G.isKnot_def.mp hG]
  exact odd_one

end GridDiagram

end TauCeti
