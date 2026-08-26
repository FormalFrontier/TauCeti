/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import TauCeti.Algebra.Bigraded.Basic
public import TauCeti.KnotTheory.Grid.Determinant
public import TauCeti.KnotTheory.Grid.Grading.Chain
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# The graded Euler characteristic of the grid chain module

`Grading/Chain.lean` decomposes the grid chain module of a diagram with an odd number of link
components into its homogeneous pieces, one for each pair (`O`-Maslov grading, Alexander grading),
and `Determinant.lean` evaluates the alternating Alexander state sum of a grid diagram as a
determinant. This file joins the two: the graded Euler characteristic of the bigraded grid chain
module *is* the state sum, hence is a normalized grid-determinant expression.

Freezing one Alexander degree `a` leaves a module graded by the `O`-Maslov degree alone, and its
Euler characteristic is Mathlib's `GradedObject.eulerChar` for the complex shape
`ComplexShape.down ℤ`, the shape of a differential dropping the Maslov grading by one. That
integer, `OddComponentGridDiagram.alexanderEulerChar`, is the alternating count of grid states in
Alexander degree `a` weighted by the parity of their Maslov grading. Applying the generic
`Bigraded.euler` map to the rank Poincaré series and then doubling its Alexander exponents gives
`OddComponentGridDiagram.gradedEulerChar`.

Two conventions are inherited rather than reinvented. The grading variable `T` is a square root of
the usual Alexander variable, exactly as in `Determinant.lean`: the summand in bidegree `(m, a)`
contributes `(-1)^m T^{2a}`, so that the graded Euler characteristic lives in the same ring as the
state sum and compares with the determinant on the nose. The Maslov grading is the one that the
grid differential drops, which is why the alternating signs are read off `ComplexShape.down ℤ`.

Nothing here needs a differential, and in particular nothing here assumes `∂² = 0`: the Euler
characteristic of a bigraded module is defined by its ranks alone. Over a field it agrees with the
Euler characteristic of a future square-zero differential; that comparison is not formalized
here. That is why Mathlib's graded-object Euler characteristic, rather than its
`HomologicalComplex` version, is the one consumed.

## Main definitions

* `TauCeti.OddComponentGridDiagram.alexanderGradedObject`: the Maslov-graded object of a fixed
  Alexander degree.
* `TauCeti.OddComponentGridDiagram.alexanderEulerChar`: its Euler characteristic.
* `TauCeti.OddComponentGridDiagram.bigradedPoincareSeries`: the Poincaré series of the grid chain
  module in its (`O`-Maslov, Alexander) bidegrees.
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
* `TauCeti.OddComponentGridDiagram.alexanderEulerChar_eq_coeff_smul_T_mul_det_weightMatrix`: the
  Euler characteristic of an Alexander degree is the corresponding coefficient of the normalized
  grid determinant expression.

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

private theorem maslovOℤ_mem_maslovSupport {a : ℤ} {x : GridState n}
    (hx : G.alexanderℤ x = a) :
    G.1.maslovOℤ x ∈ G.maslovSupport a :=
  (G.mem_maslovSupport_iff a _).2 ⟨x, Prod.ext (G.bidegree_fst x) (hx ▸ G.bidegree_snd x)⟩

private theorem filter_bidegree_eq (a m : ℤ) :
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

/-- The degree-`m` component of the Maslov-graded object in Alexander degree `a`. -/
@[simp]
theorem alexanderGradedObject_apply (R : Type*) [Ring R] (a m : ℤ) :
    G.alexanderGradedObject R a m = ModuleCat.of R (G.BigradedChainPiece R (m, a)) := by
  rw [alexanderGradedObject]

/-- The rank of the Maslov-graded object in degree `m` is the number of grid states of bidegree
`(m, a)`. -/
theorem finrank_alexanderGradedObject (R : Type*) [Ring R] [StrongRankCondition R] (a m : ℤ) :
    Module.finrank R (G.alexanderGradedObject R a m) =
      (Finset.univ.filter fun x : GridState n => G.bidegree x = (m, a)).card := by
  rw [G.alexanderGradedObject_apply R a m]
  exact G.finrank_bigradedChainPiece R (m, a)

private theorem finrankSupport_alexanderGradedObject_subset (R : Type*) [Ring R]
    [StrongRankCondition R]
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
@[simp]
theorem alexanderEulerChar_eq_zero_of_notMem (R : Type*) [Ring R] [StrongRankCondition R] {a : ℤ}
    (ha : a ∉ G.alexanderSupport) : G.alexanderEulerChar R a = 0 := by
  rw [G.alexanderEulerChar_eq_sum_states R a, Finset.filter_eq_empty_iff.2, Finset.sum_empty]
  exact fun x _ hx => ha ((G.mem_alexanderSupport_iff a).2 ⟨x, hx⟩)

/-! ### The graded Euler characteristic -/

/-- The Poincaré series of the bigraded grid chain module in the standard
(`O`-Maslov, Alexander) convention. -/
noncomputable def bigradedPoincareSeries (R : Type*) [Semiring R] : Bigraded.Series :=
  ∑ g ∈ G.bidegreeSupport, AddMonoidAlgebra.single g
    (Module.finrank R (G.BigradedChainPiece R g))

/-- The coefficient of the grid-chain Poincaré series in a bidegree is the rank of that
homogeneous piece. -/
@[simp]
theorem coeff_bigradedPoincareSeries (R : Type*) [Semiring R] [StrongRankCondition R]
    (g : ℤ × ℤ) :
    (G.bigradedPoincareSeries R).coeff g = Module.finrank R (G.BigradedChainPiece R g) := by
  classical
  by_cases hg : g ∈ G.bidegreeSupport
  · simp [bigradedPoincareSeries, Finsupp.single_apply, hg]
  · have hzero : Module.finrank R (G.BigradedChainPiece R g) = 0 :=
      Nat.eq_zero_of_not_pos fun h => hg ((G.finrank_bigradedChainPiece_pos_iff R g).1 h)
    simp [bigradedPoincareSeries, Finsupp.single_apply, hg, hzero]

/-- The total dimension of the grid-chain Poincaré series is the number `n!` of grid states. -/
@[simp]
theorem totalDim_bigradedPoincareSeries (R : Type*) [Semiring R] [StrongRankCondition R] :
    Bigraded.totalDim (G.bigradedPoincareSeries R) = n.factorial := by
  rw [bigradedPoincareSeries, map_sum]
  simp_rw [Bigraded.totalDim_single]
  exact G.sum_finrank_bigradedChainPiece R

/-- The ring homomorphism that doubles every Laurent-polynomial exponent. -/
private noncomputable def doubleExponents : ℤ[T;T⁻¹] →+* ℤ[T;T⁻¹] :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (nsmulAddMonoidHom 2 : ℤ →+ ℤ)

/-- Doubling exponents sends a Laurent monomial in degree `a` to one in degree `2a`. -/
private theorem doubleExponents_single (a z : ℤ) :
    doubleExponents (AddMonoidAlgebra.single a z) = AddMonoidAlgebra.single (2 * a) z := by
  rw [doubleExponents, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single]
  rfl

/-- The graded Euler characteristic obtained by applying `Bigraded.euler` to the rank Poincaré
series of the bigraded grid chain module and then doubling every Alexander exponent.

The grading variable `T` is a square root of the Alexander variable, as in `Determinant.lean`, so
Alexander degree `a` contributes the monomial `T^{2a}`. -/
noncomputable def gradedEulerChar (R : Type*) [Semiring R] : ℤ[T;T⁻¹] :=
  doubleExponents (Bigraded.euler (G.bigradedPoincareSeries R))

/-- **The graded Euler characteristic is the alternating Alexander state sum.** Regrouping the
states of the diagram by their bidegree turns the rank-weighted sum over occupied degrees into the
sum over states. -/
theorem gradedEulerChar_eq_stateSum (R : Type*) [Semiring R] [StrongRankCondition R] :
    G.gradedEulerChar R = G.1.stateSum := by
  rw [gradedEulerChar, bigradedPoincareSeries, map_sum, map_sum]
  rw [GridDiagram.stateSum_def,
    ← Finset.sum_fiberwise_of_maps_to (g := fun x : GridState n => G.bidegree x)
      (t := G.bidegreeSupport) (fun x _ => (G.mem_bidegreeSupport_iff _).2 ⟨x, rfl⟩)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rcases g with ⟨m, a⟩
  rw [Bigraded.euler_single, map_mul, map_natCast, doubleExponents_single,
    G.finrank_bigradedChainPiece R]
  have hconst : ∑ x ∈ Finset.univ.filter (fun x : GridState n => G.bidegree x = (m, a)),
        ((G.1.maslovOℤ x).negOnePow : ℤˣ) • (T (G.1.alexanderTwoℤ x) : ℤ[T;T⁻¹]) =
      ∑ _x ∈ Finset.univ.filter (fun x : GridState n => G.bidegree x = (m, a)),
        (m.negOnePow : ℤˣ) • (T (2 * a) : ℤ[T;T⁻¹]) :=
    Finset.sum_congr rfl fun x hx => by
      have hg := (Finset.mem_filter.1 hx).2
      have hm : G.1.maslovOℤ x = m := by
        rw [← G.bidegree_fst x, hg]
      have ha : G.1.alexanderTwoℤ x = 2 * a := by
        rw [← G.two_mul_alexanderℤ x, ← G.bidegree_snd x, hg]
      rw [hm, ha]
  rw [hconst, Finset.sum_const, nsmul_eq_mul, Units.smul_def, zsmul_eq_mul,
    LaurentPolynomial.single_eq_C_mul_T]
  have hC : LaurentPolynomial.C (m.negOnePow : ℤ) =
      ((m.negOnePow : ℤ) : ℤ[T;T⁻¹]) :=
    map_intCast LaurentPolynomial.C (m.negOnePow : ℤ)
  rw [hC]

/-- **The graded Euler characteristic is a normalized grid-determinant expression.** Combining
`OddComponentGridDiagram.gradedEulerChar_eq_stateSum` with the grid determinant formula, the
graded Euler characteristic of the bigraded grid chain module is a sign times a monomial times the
determinant of the weight matrix of the diagram. -/
theorem gradedEulerChar_eq_smul_T_mul_det_weightMatrix (R : Type*) [Semiring R]
    [StrongRankCondition R] :
    G.gradedEulerChar R =
      (Equiv.Perm.sign G.1.O.toPerm * ((n : ℤ) + 1).negOnePow) •
        (T G.1.alexanderTwoShift * G.1.weightMatrix.det) := by
  rw [G.gradedEulerChar_eq_stateSum R, G.1.stateSum_eq_smul_T_mul_det_weightMatrix]

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

/-- The graded Euler characteristic is the generating function of the Euler characteristics in
the occupied Alexander degrees, with doubled exponents for the square-root variable. -/
theorem gradedEulerChar_eq_sum_alexanderSupport (R : Type*) [Ring R]
    [StrongRankCondition R] :
    G.gradedEulerChar R = ∑ a ∈ G.alexanderSupport, G.alexanderEulerChar R a • T (2 * a) := by
  rw [G.gradedEulerChar_eq_stateSum R]
  symm
  rw [GridDiagram.stateSum_def,
    ← Finset.sum_fiberwise_of_maps_to (g := fun x : GridState n => G.alexanderℤ x)
      (t := G.alexanderSupport)
      (fun x _ => (G.mem_alexanderSupport_iff _).2 ⟨x, rfl⟩)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [G.alexanderEulerChar_eq_sum_states R a, Finset.sum_smul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← (Finset.mem_filter.1 hx).2, G.two_mul_alexanderℤ x, Units.smul_def, zsmul_eq_mul]

/-- The coefficients of the graded Euler characteristic, degree by degree. -/
theorem coeff_gradedEulerChar (R : Type*) [Ring R] [StrongRankCondition R] (k : ℤ) :
    (G.gradedEulerChar R).coeff k =
      ∑ a ∈ G.alexanderSupport, if 2 * a = k then G.alexanderEulerChar R a else 0 := by
  rw [G.gradedEulerChar_eq_sum_alexanderSupport R]
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply',
    AddMonoidAlgebra.coeff_smul_apply, T_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- Only even exponents occur in the graded Euler characteristic: the grading variable is a square
root of the Alexander variable, and the Alexander gradings of an odd-component diagram are
integers. -/
@[simp]
theorem coeff_gradedEulerChar_of_odd (R : Type*) [Ring R] [StrongRankCondition R] {k : ℤ}
    (hk : Odd k) : (G.gradedEulerChar R).coeff k = 0 := by
  rw [G.coeff_gradedEulerChar R k]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [ite_eq_right_iff]
  exact fun h => ((Int.not_even_iff_odd.mpr hk) ⟨a, by omega⟩).elim

/-- The graded Euler characteristic loses nothing: its coefficient in exponent `2a` is the Euler
characteristic of Alexander degree `a`. -/
@[simp]
theorem coeff_gradedEulerChar_two_mul (R : Type*) [Ring R] [StrongRankCondition R] (a : ℤ) :
    (G.gradedEulerChar R).coeff (2 * a) = G.alexanderEulerChar R a := by
  rw [G.coeff_gradedEulerChar R (2 * a)]
  by_cases ha : a ∈ G.alexanderSupport
  · rw [Finset.sum_eq_single_of_mem a ha fun b _ hb => by
      rw [ite_eq_right_iff]
      omega]
    simp
  · rw [G.alexanderEulerChar_eq_zero_of_notMem R ha]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [ite_eq_right_iff]
    intro h
    have hba : b = a := by omega
    subst b
    exact (ha hb).elim

/-- **The Euler characteristics of the Alexander degrees are the coefficients of the normalized
grid-determinant expression.** The alternating count of grid states of Alexander degree `a`,
weighted by the parity of their Maslov grading, is the coefficient of `T^{2a}` in the expression of
`GridDiagram.stateSum_eq_smul_T_mul_det_weightMatrix`. -/
theorem alexanderEulerChar_eq_coeff_smul_T_mul_det_weightMatrix (R : Type*) [Ring R]
    [StrongRankCondition R] (a : ℤ) :
    G.alexanderEulerChar R a =
      ((Equiv.Perm.sign G.1.O.toPerm * ((n : ℤ) + 1).negOnePow) •
        (T G.1.alexanderTwoShift * G.1.weightMatrix.det) : ℤ[T;T⁻¹]).coeff (2 * a) := by
  rw [← G.gradedEulerChar_eq_smul_T_mul_det_weightMatrix R, G.coeff_gradedEulerChar_two_mul R a]

end OddComponentGridDiagram

end TauCeti
