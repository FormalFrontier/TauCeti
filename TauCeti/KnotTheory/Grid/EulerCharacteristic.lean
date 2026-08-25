/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import TauCeti.KnotTheory.Grid.Determinant
public import TauCeti.KnotTheory.Grid.Grading.Chain
public import TauCeti.KnotTheory.Grid.SmallGrid.Gradings

/-!
# The graded Euler characteristic of the grid chain module

`Grading/Chain.lean` decomposes the grid chain module of a diagram with an odd number of link
components into its homogeneous pieces, one for each pair (`O`-Maslov grading, Alexander grading),
and `Determinant.lean` evaluates the alternating Alexander state sum of a grid diagram as a
determinant. This file joins the two: the graded Euler characteristic of the bigraded grid chain
module *is* the state sum, hence is the grid determinant.

Freezing one Alexander degree `a` leaves a module graded by the `O`-Maslov degree alone, and its
Euler characteristic is Mathlib's `GradedObject.eulerChar` for the complex shape
`ComplexShape.down ℤ`, the shape of a differential dropping the Maslov grading by one. That
integer, `OddComponentGridDiagram.alexanderEulerChar`, is the alternating count of grid states in
Alexander degree `a` weighted by the parity of their Maslov grading. Assembling those integers
into a Laurent polynomial gives `OddComponentGridDiagram.gradedEulerChar`.

Two conventions are inherited rather than reinvented. The grading variable `T` is a square root of
the usual Alexander variable, exactly as in `Determinant.lean`: the summand in bidegree `(m, a)`
contributes `(-1)^m T^{2a}`, so that the graded Euler characteristic lives in the same ring as the
state sum and compares with the determinant on the nose. The Maslov grading is the one that the
grid differential drops, which is why the alternating signs are read off `ComplexShape.down ℤ`.

Nothing here needs a differential, and in particular nothing here assumes `∂² = 0`: the Euler
characteristic of a bigraded module is defined by its ranks alone, and once a square-zero
differential on it is available the two Euler characteristics agree, since every homogeneous piece
here has finite rank. That is why Mathlib's graded-object Euler characteristic, rather than its
`HomologicalComplex` version, is the one consumed.

## Main definitions

* `TauCeti.OddComponentGridDiagram.alexanderSupport`: the Alexander degrees occupied by grid
  states.
* `TauCeti.OddComponentGridDiagram.maslovSupport`: the Maslov degrees occupied in a fixed
  Alexander degree.
* `TauCeti.OddComponentGridDiagram.alexanderGradedObject`: the Maslov-graded object of a fixed
  Alexander degree.
* `TauCeti.OddComponentGridDiagram.alexanderEulerChar`: its Euler characteristic.
* `TauCeti.OddComponentGridDiagram.gradedEulerChar`: the graded Euler characteristic of the
  bigraded grid chain module, as a Laurent polynomial in the square root of the Alexander variable.

## Main results

* `TauCeti.OddComponentGridDiagram.alexanderEulerChar_eq_sum_states`: the Euler characteristic in
  one Alexander degree is the alternating count of the grid states of that degree.
* `TauCeti.OddComponentGridDiagram.gradedEulerChar_eq_stateSum`: the graded Euler characteristic is
  the alternating Alexander state sum.
* `TauCeti.OddComponentGridDiagram.gradedEulerChar_eq_smul_T_mul_det_weightMatrix`: the graded Euler
  characteristic is a sign times a monomial times the grid determinant.
* `TauCeti.OddComponentGridDiagram.sum_alexanderEulerChar_eq_zero`: the ungraded Euler
  characteristic of a grid chain module of size at least two vanishes.
* `TauCeti.OddComponentGridDiagram.alexanderEulerChar_eq_coeff_det`: the Euler characteristic of
  an Alexander degree is the corresponding coefficient of the grid determinant.
* `TauCeti.OddComponentGridDiagram.gradedEulerChar_twoByTwo`: the graded Euler characteristic of
  the standard `2 × 2` unknot grid is `1 - T⁻²`.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.4, "Euler
characteristic = Alexander polynomial, via the grid determinant formula", by supplying the Euler
characteristic side of that equation; the grid determinant side is `Determinant.lean`. The
conventions follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.3 and
Chapter 4.
-/

public section

open CategoryTheory LaurentPolynomial

namespace TauCeti

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

/-! ### The occupied degrees -/

/-- The Alexander degrees occupied by the grid states of a diagram. -/
noncomputable def alexanderSupport : Finset ℤ :=
  G.bidegreeSupport.image Prod.snd

/-- An Alexander degree is occupied exactly when some grid state has it. -/
@[simp]
theorem mem_alexanderSupport_iff (a : ℤ) :
    a ∈ G.alexanderSupport ↔ ∃ x : GridState n, G.alexanderℤ x = a := by
  simp only [alexanderSupport, Finset.mem_image, mem_bidegreeSupport_iff]
  constructor
  · rintro ⟨g, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (G.bidegree_snd x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨G.bidegree x, ⟨x, rfl⟩, G.bidegree_snd x⟩

/-- The `O`-Maslov degrees occupied by the grid states of a fixed Alexander degree. -/
noncomputable def maslovSupport (a : ℤ) : Finset ℤ :=
  (G.bidegreeSupport.filter fun g => g.2 = a).image Prod.fst

/-- A Maslov degree is occupied in Alexander degree `a` exactly when some grid state has
bidegree `(m, a)`. -/
@[simp]
theorem mem_maslovSupport_iff (a m : ℤ) :
    m ∈ G.maslovSupport a ↔ ∃ x : GridState n, G.bidegree x = (m, a) := by
  simp only [maslovSupport, Finset.mem_image, Finset.mem_filter, mem_bidegreeSupport_iff]
  constructor
  · rintro ⟨g, ⟨⟨x, rfl⟩, hg⟩, rfl⟩
    exact ⟨x, Prod.ext rfl hg⟩
  · rintro ⟨x, hx⟩
    exact ⟨(m, a), ⟨⟨x, hx⟩, rfl⟩, rfl⟩

/-- A grid state of Alexander degree `a` occupies a Maslov degree of that Alexander degree. -/
theorem maslovOℤ_mem_maslovSupport {a : ℤ} {x : GridState n} (hx : G.alexanderℤ x = a) :
    G.1.maslovOℤ x ∈ G.maslovSupport a :=
  (G.mem_maslovSupport_iff a _).2 ⟨x, Prod.ext (G.bidegree_fst x) (hx ▸ G.bidegree_snd x)⟩

/-- The grid states of bidegree `(m, a)` are the states of Alexander degree `a` whose Maslov
degree is `m`. -/
theorem filter_bidegree_eq (a m : ℤ) :
    (Finset.univ.filter fun x : GridState n => G.bidegree x = (m, a)) =
      (Finset.univ.filter fun x : GridState n => G.alexanderℤ x = a).filter
        fun x => G.1.maslovOℤ x = m := by
  rw [Finset.filter_filter]
  refine Finset.filter_congr fun x _ => ?_
  rw [Prod.ext_iff, G.bidegree_fst x, G.bidegree_snd x]
  exact and_comm

/-! ### The Euler characteristic of one Alexander degree -/

/-- The `O`-Maslov-graded object underlying the grid chain module in a fixed Alexander degree. -/
noncomputable def alexanderGradedObject (R : Type*) [Ring R] (a : ℤ) :
    GradedObject ℤ (ModuleCat R) :=
  fun m => ModuleCat.of R (G.BigradedChainPiece R (m, a))

/-- The rank of the Maslov-graded object in degree `m` is the number of grid states of bidegree
`(m, a)`. -/
theorem finrank_alexanderGradedObject (R : Type*) [Ring R] [StrongRankCondition R] (a m : ℤ) :
    Module.finrank R (G.alexanderGradedObject R a m) =
      (Finset.univ.filter fun x : GridState n => G.bidegree x = (m, a)).card :=
  G.finrank_bigradedChainPiece R (m, a)

/-- The Maslov-graded object of an Alexander degree has rank zero outside the occupied Maslov
degrees. -/
theorem finrankSupport_alexanderGradedObject_subset (R : Type*) [Ring R] [StrongRankCondition R]
    (a : ℤ) :
    GradedObject.finrankSupport (G.alexanderGradedObject R a) ⊆ (G.maslovSupport a : Set ℤ) := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro m hm
  rw [G.finrank_alexanderGradedObject R a m, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  exact hm (Finset.mem_coe.2 ((G.mem_maslovSupport_iff a m).2 ⟨x, hx⟩))

/-- The Euler characteristic of the grid chain module in a fixed Alexander degree, taken with
respect to the `O`-Maslov grading.

The complex shape is `ComplexShape.down ℤ` because the grid differential drops the Maslov
grading by one. -/
noncomputable def alexanderEulerChar (R : Type*) [Ring R] (a : ℤ) : ℤ :=
  GradedObject.eulerChar (ComplexShape.down ℤ) (G.alexanderGradedObject R a)

/-- The Euler characteristic of an Alexander degree, as a finite alternating sum of the ranks of
its homogeneous pieces. -/
theorem alexanderEulerChar_eq_sum_maslovSupport (R : Type*) [Ring R] [StrongRankCondition R]
    (a : ℤ) :
    G.alexanderEulerChar R a =
      ∑ m ∈ G.maslovSupport a, (m.negOnePow : ℤ) *
        (Finset.univ.filter fun x : GridState n => G.bidegree x = (m, a)).card := by
  rw [alexanderEulerChar, GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset _ _ _
    (G.finrankSupport_alexanderGradedObject_subset R a)]
  exact Finset.sum_congr rfl fun m _ => by
    rw [G.finrank_alexanderGradedObject R a m, ComplexShape.χ,
      ComplexShape.eulerCharSignsDownInt_χ]

/-- The Euler characteristic of an Alexander degree is the alternating count of the grid states of
that degree, weighted by the parity of their `O`-Maslov grading. -/
theorem alexanderEulerChar_eq_sum_states (R : Type*) [Ring R] [StrongRankCondition R] (a : ℤ) :
    G.alexanderEulerChar R a =
      ∑ x ∈ Finset.univ.filter fun x : GridState n => G.alexanderℤ x = a,
        ((G.1.maslovOℤ x).negOnePow : ℤ) := by
  rw [G.alexanderEulerChar_eq_sum_maslovSupport R a,
    ← Finset.sum_fiberwise_of_maps_to (g := fun x : GridState n => G.1.maslovOℤ x)
      (t := G.maslovSupport a)
      (fun x hx => G.maslovOℤ_mem_maslovSupport (Finset.mem_filter.1 hx).2)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hconst : ∑ x ∈ (Finset.univ.filter fun x : GridState n => G.alexanderℤ x = a).filter
        (fun x => G.1.maslovOℤ x = m), ((G.1.maslovOℤ x).negOnePow : ℤ) =
      ∑ _x ∈ (Finset.univ.filter fun x : GridState n => G.alexanderℤ x = a).filter
        (fun x => G.1.maslovOℤ x = m), (m.negOnePow : ℤ) :=
    Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2]
  rw [hconst, G.filter_bidegree_eq a m, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- In an unoccupied Alexander degree the Euler characteristic vanishes. -/
theorem alexanderEulerChar_eq_zero_of_notMem (R : Type*) [Ring R] [StrongRankCondition R] {a : ℤ}
    (ha : a ∉ G.alexanderSupport) : G.alexanderEulerChar R a = 0 := by
  rw [G.alexanderEulerChar_eq_sum_states R a, Finset.filter_eq_empty_iff.2, Finset.sum_empty]
  exact fun x _ hx => ha ((G.mem_alexanderSupport_iff a).2 ⟨x, hx⟩)

/-- The Euler characteristic of an Alexander degree does not depend on the coefficient ring. -/
theorem alexanderEulerChar_eq_alexanderEulerChar (R S : Type*) [Ring R] [StrongRankCondition R]
    [Ring S] [StrongRankCondition S] (a : ℤ) : G.alexanderEulerChar R a =
      G.alexanderEulerChar S a := by
  rw [G.alexanderEulerChar_eq_sum_states R a, G.alexanderEulerChar_eq_sum_states S a]

/-! ### The graded Euler characteristic -/

/-- The graded Euler characteristic of the bigraded grid chain module: the Euler characteristic of
each Alexander degree, weighted by the corresponding monomial.

The grading variable `T` is a square root of the Alexander variable, as in `Determinant.lean`, so
Alexander degree `a` contributes the monomial `T^{2a}`. -/
noncomputable def gradedEulerChar (R : Type*) [Ring R] : ℤ[T;T⁻¹] :=
  ∑ a ∈ G.alexanderSupport, G.alexanderEulerChar R a • T (2 * a)

/-- **The graded Euler characteristic is the alternating Alexander state sum.** Regrouping the
states of the diagram by their bidegree turns the rank-weighted sum over occupied degrees into the
sum over states. -/
theorem gradedEulerChar_eq_stateSum (R : Type*) [Ring R] [StrongRankCondition R] :
    G.gradedEulerChar R = G.1.stateSum := by
  rw [gradedEulerChar, GridDiagram.stateSum_def,
    ← Finset.sum_fiberwise_of_maps_to (g := fun x : GridState n => G.alexanderℤ x)
      (t := G.alexanderSupport)
      (fun x _ => (G.mem_alexanderSupport_iff _).2 ⟨x, rfl⟩)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [G.alexanderEulerChar_eq_sum_states R a, Finset.sum_smul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← (Finset.mem_filter.1 hx).2, G.two_mul_alexanderℤ x, Units.smul_def, zsmul_eq_mul]

/-- **The graded Euler characteristic is the grid determinant.** Combining
`OddComponentGridDiagram.gradedEulerChar_eq_stateSum` with the grid determinant formula, the
graded Euler characteristic of the bigraded grid chain module is a sign times a monomial times the
determinant of the weight matrix of the diagram. -/
theorem gradedEulerChar_eq_smul_T_mul_det_weightMatrix (R : Type*) [Ring R]
    [StrongRankCondition R] :
    G.gradedEulerChar R =
      (Equiv.Perm.sign G.1.O.toPerm * ((n : ℤ) + 1).negOnePow) •
        (T G.1.alexanderTwoShift * G.1.weightMatrix.det) := by
  rw [G.gradedEulerChar_eq_stateSum R, G.1.stateSum_eq_smul_T_mul_det_weightMatrix]

/-- The graded Euler characteristic does not depend on the coefficient ring. -/
theorem gradedEulerChar_eq_gradedEulerChar (R S : Type*) [Ring R] [StrongRankCondition R]
    [Ring S] [StrongRankCondition S] : G.gradedEulerChar R = G.gradedEulerChar S := by
  rw [G.gradedEulerChar_eq_stateSum R, G.gradedEulerChar_eq_stateSum S]

/-- The ungraded Euler characteristic of the grid chain module vanishes on every grid of size at
least two: the Euler characteristics of the Alexander degrees cancel.

This is the graded Euler characteristic evaluated at `T = 1`, where the weight matrix of the
determinant formula acquires two equal rows. -/
theorem sum_alexanderEulerChar_eq_zero (R : Type*) [Ring R] [StrongRankCondition R] (hn : 2 ≤ n) :
    ∑ a ∈ G.alexanderSupport, G.alexanderEulerChar R a = 0 := by
  rw [← G.1.sum_negOnePow_maslovOℤ_eq_zero hn,
    ← Finset.sum_fiberwise_of_maps_to (g := fun x : GridState n => G.alexanderℤ x)
      (t := G.alexanderSupport)
      (fun x _ => (G.mem_alexanderSupport_iff _).2 ⟨x, rfl⟩)]
  exact Finset.sum_congr rfl fun a _ => G.alexanderEulerChar_eq_sum_states R a

/-! ### Reading the Alexander degrees off the coefficients -/

/-- The coefficients of the graded Euler characteristic, degree by degree. -/
theorem coeff_gradedEulerChar (R : Type*) [Ring R] (k : ℤ) :
    (G.gradedEulerChar R).coeff k =
      ∑ a ∈ G.alexanderSupport, if 2 * a = k then G.alexanderEulerChar R a else 0 := by
  simp only [gradedEulerChar, AddMonoidAlgebra.coeff_sum, Finset.sum_apply',
    AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- Only even exponents occur in the graded Euler characteristic: the grading variable is a square
root of the Alexander variable, and the Alexander gradings of an odd-component diagram are
integers. -/
theorem coeff_gradedEulerChar_of_not_even (R : Type*) [Ring R] {k : ℤ}
    (hk : ¬ Even k) : (G.gradedEulerChar R).coeff k = 0 := by
  rw [G.coeff_gradedEulerChar R k]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [ite_eq_right_iff]
  exact fun h => absurd ⟨a, by omega⟩ hk

/-- The graded Euler characteristic loses nothing: its coefficient in exponent `2a` is the Euler
characteristic of Alexander degree `a`. -/
theorem coeff_gradedEulerChar_two_mul (R : Type*) [Ring R] [StrongRankCondition R] (a : ℤ) :
    (G.gradedEulerChar R).coeff (2 * a) = G.alexanderEulerChar R a := by
  rw [G.coeff_gradedEulerChar R (2 * a)]
  by_cases ha : a ∈ G.alexanderSupport
  · rw [Finset.sum_eq_single_of_mem a ha fun b _ hb => by
      rw [ite_eq_right_iff]; exact fun h => absurd (show b = a by omega) hb]
    simp
  · rw [G.alexanderEulerChar_eq_zero_of_notMem R ha]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [ite_eq_right_iff]
    exact fun h => absurd (show a ∈ G.alexanderSupport from (show b = a by omega) ▸ hb) ha

/-- **The Euler characteristics of the Alexander degrees are the coefficients of the grid
determinant.** The alternating count of grid states of Alexander degree `a`, weighted by the parity
of their Maslov grading, is the coefficient of `T^{2a}` in the determinant expression of
`GridDiagram.stateSum_eq_smul_T_mul_det_weightMatrix`. -/
theorem alexanderEulerChar_eq_coeff_det (R : Type*) [Ring R] [StrongRankCondition R] (a : ℤ) :
    G.alexanderEulerChar R a =
      ((Equiv.Perm.sign G.1.O.toPerm * ((n : ℤ) + 1).negOnePow) •
        (T G.1.alexanderTwoShift * G.1.weightMatrix.det) : ℤ[T;T⁻¹]).coeff (2 * a) := by
  rw [← G.gradedEulerChar_eq_smul_T_mul_det_weightMatrix R, G.coeff_gradedEulerChar_two_mul R a]

/-! ### The smallest unknot grid -/

/-- The standard `2 × 2` unknot grid diagram, as an odd-component grid diagram: it presents a
knot, so its component count is one. -/
abbrev twoByTwo : OddComponentGridDiagram 2 :=
  ⟨GridDiagram.twoByTwo, by
    have h : GridDiagram.twoByTwo.componentCount = 1 :=
      GridDiagram.unknot_zero ▸ (GridDiagram.isKnot_def _).1 (GridDiagram.isKnot_unknot 0)
    rw [h]
    exact odd_one⟩

/-- The graded Euler characteristic of the standard `2 × 2` unknot grid is `1 - T⁻²`.

Its two grid states sit in bidegrees `(-1, -1)` and `(0, 0)`, so each of the two occupied
Alexander degrees contributes a single generator, and the two Maslov parities are opposite. In the
Alexander variable `t = T²` the answer reads `1 - t⁻¹`, which is the Euler characteristic of one
copy of the stabilization factor `W = 𝔽 ⊕ 𝔽` in bidegrees `(0, 0)` and `(-1, -1)`: the grid-size
dependence of the fully blocked theory is already visible in its Euler characteristic. -/
theorem gradedEulerChar_twoByTwo (R : Type*) [Ring R] [StrongRankCondition R] :
    twoByTwo.gradedEulerChar R = 1 - T (-2) := by
  have huniv : (Finset.univ : Finset (GridState 2)) =
      {GridState.twoByTwoId, GridState.twoByTwoSwap} := by
    ext x
    simpa using GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x
  rw [gradedEulerChar_eq_stateSum, GridDiagram.stateSum_def, huniv,
    Finset.sum_insert (by
      simp only [Finset.mem_singleton]
      exact GridState.twoByTwoId_ne_twoByTwoSwap), Finset.sum_singleton,
    GridDiagram.maslovOℤ_twoByTwo_twoByTwoId, GridDiagram.alexanderTwoℤ_twoByTwo_twoByTwoId,
    GridDiagram.maslovOℤ_twoByTwo_twoByTwoSwap, GridDiagram.alexanderTwoℤ_twoByTwo_twoByTwoSwap]
  simp [Int.negOnePow_neg, Units.smul_def, sub_eq_add_neg, add_comm]

end OddComponentGridDiagram

end TauCeti
