/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.MvPolynomial.Degrees
public import TauCeti.KnotTheory.Grid.Complex
public import TauCeti.KnotTheory.Grid.Grading.MarkingCount
import TauCeti.KnotTheory.Grid.Rectangle.Count
import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# The unblocked grid complex `GC⁻`

The fully blocked complex of `Complex.lean` counts only rectangles that avoid every marking,
so it forgets the `O`-markings entirely. The *unblocked* complex `GC⁻` remembers them:
it is the free module on grid states over the polynomial ring `R[V₀, …, V_{n-1}]`, one variable
`V_c` for the `O`-marking of column `c`, and its differential

`∂⁻ x = ∑_y ∑_r V^{O(r)} · y`

runs over the empty rectangles `r` from `x` to `y` carrying no `X`-marking, each weighted by the
monomial `V^{O(r)} = ∏ V_c` over the columns whose `O`-marking the rectangle covers. This is the
theory that survives (de)stabilization and whose homology is a module over `R[U]`. The simply
blocked theory is obtained by setting one selected variable, conventionally `V₀`, to zero; setting
every variable to zero gives the square-centred fully blocked count once the canonical
`GridRectangle.AvoidsMarkings` predicate uses that same marking region.

Two conventions are fixed here.

*Which region carries a marking.* Markings sit at the centres of their squares, so a rectangle
carries the markings of the squares it covers, `GridRectangle.coveredSquares`, not those of the
grid points in its open interior. That is the region the Maslov and Alexander grading changes are
computed against in `Grading/MarkingCount.lean`, and it is the region used throughout this file.
The Lane G.3 predicate `GridRectangle.AvoidsMarkings` still tests the open interior; aligning it
with the square-centred convention is a separate correction to that predicate, so no result here
is phrased in terms of it.

*Which grading the variables carry.* Giving `V_c` bidegree `(-2, -1)` makes the differential
homogeneous of bidegree `(-1, 0)`: `maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one` and
`alexander_sub_card_OColumns_eq_alexander` say exactly that the term `V^{O(r)} · y` contributed by
a rectangle `r` from `x` to `y` has Maslov grading `M_O(x) - 1` and Alexander grading `A(x)`. The
Maslov statement needs the rectangle to be empty; the Alexander statement holds for every
`X`-avoiding rectangle.

The differential is defined over an arbitrary commutative coefficient ring. It squares to zero
only in characteristic two: over a general ring the rectangle counts must be corrected by a sign
assignment, a later stage of the roadmap.

## Main definitions

* `TauCeti.GridDiagram.OColumns`: the columns whose `O`-marking a rectangle covers.
* `TauCeti.GridDiagram.OMonomial`: the monomial `V^{O(r)}` weighting a rectangle.
* `TauCeti.GridDiagram.unblockedRectangles`: the empty rectangles carrying no `X`-marking.
* `TauCeti.GridChainMinus`: the free `R[V₀, …, V_{n-1}]`-module on grid states.
* `TauCeti.GridDiagram.unblockedDifferential`: the unblocked differential, as a linear map over
  the polynomial ring.

## Main results

* `TauCeti.GridDiagram.card_OColumns`: the number of covered `O`-columns is the number of
  `O`-markings among the covered squares.
* `TauCeti.GridDiagram.totalDegree_OMonomial`: the weight of a rectangle is a squarefree monomial
  whose degree is the number of `O`-markings the rectangle covers.
* `TauCeti.GridDiagram.unblockedDifferentialOnGenerator_support_subset`: the differential of a
  generator is supported on the column transpositions of that generator.
* `TauCeti.GridDiagram.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one`,
  `TauCeti.GridDiagram.alexander_sub_card_OColumns_eq_alexander`: the differential is homogeneous
  of bidegree `(-1, 0)` once `V_c` is given bidegree `(-2, -1)`.
* `TauCeti.GridDiagram.constantCoeff_unblockedCoefficient`: the constant term of a matrix
  coefficient counts the contributing rectangles that carry no `O`-marking either.

## References

This supplies `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and
`∂² = 0`", specifically its "Then unblocked `GC⁻` over `𝔽₂[V₁,…,Vₙ]`" clause, together with the
roadmap convention "Fix once whether differentials drop Maslov by 1 and preserve Alexander
(unblocked)". The definitions and the bidegree computation follow Ozsváth--Stipsicz--Szabó, *Grid
Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

open MvPolynomial

/-- The unblocked chain module `GC⁻` of a grid diagram of size `n`: the free module on grid
states over the polynomial ring `R[V₀, …, V_{n-1}]`, with one variable for each `O`-marking. -/
abbrev GridChainMinus (R : Type*) [CommSemiring R] (n : ℕ) : Type _ :=
  GridChain (MvPolynomial (Fin n) R) n

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### The `O`-monomial of a rectangle -/

/-- The columns whose `O`-marking lies in the squares a toroidal rectangle covers.

The `O`-markings of a grid diagram are indexed by their columns, so this finite set of columns is
the index set of the variables occurring in the rectangle's weight. -/
noncomputable def OColumns (r : GridRectangle n) : Finset (Fin n) :=
  Finset.univ.filter fun c => (c, G.O c) ∈ r.coveredSquares

/-- A column is a covered `O`-column exactly when its `O`-marking is a covered square. -/
@[simp]
theorem mem_OColumns {r : GridRectangle n} {c : Fin n} :
    c ∈ G.OColumns r ↔ (c, G.O c) ∈ r.coveredSquares := by
  simp [OColumns]

/-- The covered `O`-markings are exactly the markings of the covered `O`-columns. -/
theorem OSet_inter_coveredSquares (r : GridRectangle n) :
    G.OSet ∩ r.coveredSquares = (G.OColumns r).image fun c => (c, G.O c) := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_image, mem_OColumns, mem_OSet]
  constructor
  · rintro ⟨hp, hcov⟩
    exact ⟨p.1, by rwa [hp], by rw [hp]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨rfl, hc⟩

/-- The number of covered `O`-columns is the number of `O`-markings among the covered squares:
a grid diagram has exactly one `O`-marking in each column. -/
theorem card_OColumns (r : GridRectangle n) :
    (G.OColumns r).card = (G.OSet ∩ r.coveredSquares).card := by
  rw [OSet_inter_coveredSquares, Finset.card_image_of_injective]
  exact fun a b hab => congrArg Prod.fst hab

/-- A rectangle covers no `O`-column exactly when its covered squares carry no `O`-marking. -/
theorem OColumns_eq_empty_iff (r : GridRectangle n) :
    G.OColumns r = ∅ ↔ Disjoint r.coveredSquares G.OSet := by
  rw [← Finset.card_eq_zero, card_OColumns, Finset.card_eq_zero,
    ← Finset.disjoint_iff_inter_eq_empty]
  exact disjoint_comm

variable (R : Type*) [CommSemiring R]

/-- The weight of a toroidal rectangle in the unblocked differential: the squarefree monomial
`∏ V_c` over the columns whose `O`-marking the rectangle covers.

An embedded rectangle covers each marked square at most once, so every exponent is `0` or `1`,
and the Heegaard Floer weight `V₀^{O₀(r)} ⋯ V_{n-1}^{O_{n-1}(r)}` reduces to this product. -/
noncomputable def OMonomial (r : GridRectangle n) : MvPolynomial (Fin n) R :=
  ∏ c ∈ G.OColumns r, MvPolynomial.X c

/-- The weight of a rectangle covering no `O`-marking is `1`. -/
theorem OMonomial_eq_one_of_disjoint {r : GridRectangle n}
    (h : Disjoint r.coveredSquares G.OSet) :
    G.OMonomial R r = 1 := by
  rw [OMonomial, (G.OColumns_eq_empty_iff r).mpr h, Finset.prod_empty]

/-- The weight of a rectangle, written as a monomial with an explicit exponent vector. -/
theorem OMonomial_eq_monomial (r : GridRectangle n) :
    G.OMonomial R r = monomial (∑ c ∈ G.OColumns r, Finsupp.single c 1) (1 : R) := by
  rw [OMonomial]
  generalize G.OColumns r = s
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons, ih, monomial_single_add, pow_one]

/-- The weight of a rectangle is never zero. -/
theorem OMonomial_ne_zero [Nontrivial R] (r : GridRectangle n) : G.OMonomial R r ≠ 0 := by
  rw [OMonomial_eq_monomial]
  simp

/-- The weight of a rectangle has total degree the number of `O`-markings the rectangle covers.

With each variable `V_c` in Maslov degree `-2` and Alexander degree `-1`, this says that the
weight shifts the two gradings of the target generator by `-2` and `-1` times the number of
covered `O`-markings. -/
theorem totalDegree_OMonomial [Nontrivial R] (r : GridRectangle n) :
    (G.OMonomial R r).totalDegree = (G.OColumns r).card := by
  rw [OMonomial_eq_monomial, totalDegree_monomial _ (one_ne_zero (α := R)),
    Finsupp.sum_fintype _ _ fun _ => rfl]
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp

/-! ### The rectangles the unblocked differential counts -/

/-- The rectangles counted by the unblocked differential from `x` to `y`: the empty rectangles
whose covered squares carry no `X`-marking.

Unlike the fully blocked count, `O`-markings are not forbidden; a covered `O`-marking is recorded
by the variable `V_c` in the rectangle's weight instead. -/
noncomputable def unblockedRectangles (x y : GridState n) :
    Finset (GridRectangleBetween x y) :=
  (GridRectangleBetween.emptyRectangles x y).filter fun r =>
    Disjoint r.toGridRectangle.coveredSquares G.XSet

/-- Membership in the unblocked rectangle set is emptiness together with `X`-avoidance. -/
@[simp]
theorem mem_unblockedRectangles {x y : GridState n} (r : GridRectangleBetween x y) :
    r ∈ G.unblockedRectangles x y ↔
      r.IsEmpty ∧ Disjoint r.toGridRectangle.coveredSquares G.XSet := by
  simp [unblockedRectangles]

/-- Every rectangle the unblocked differential counts is empty. -/
theorem isEmpty_of_mem_unblockedRectangles {x y : GridState n} {r : GridRectangleBetween x y}
    (hr : r ∈ G.unblockedRectangles x y) : r.IsEmpty :=
  ((G.mem_unblockedRectangles r).mp hr).1

/-- Every rectangle the unblocked differential counts covers no `X`-marking. -/
theorem disjoint_XSet_of_mem_unblockedRectangles {x y : GridState n}
    {r : GridRectangleBetween x y} (hr : r ∈ G.unblockedRectangles x y) :
    Disjoint r.toGridRectangle.coveredSquares G.XSet :=
  ((G.mem_unblockedRectangles r).mp hr).2

/-- The rectangles the unblocked differential counts are empty rectangles. -/
theorem unblockedRectangles_subset_emptyRectangles (x y : GridState n) :
    G.unblockedRectangles x y ⊆ GridRectangleBetween.emptyRectangles x y := fun _ hr =>
  (GridRectangleBetween.mem_emptyRectangles _).mpr (G.isEmpty_of_mem_unblockedRectangles hr)

/-- At most two rectangles contribute to each matrix coefficient of the unblocked
differential. -/
theorem card_unblockedRectangles_le_two (x y : GridState n) :
    (G.unblockedRectangles x y).card ≤ 2 :=
  GridRectangleBetween.card_le_two (G.unblockedRectangles x y)

/-- There is no rectangle from a grid state to itself, so the unblocked differential has no
diagonal term. -/
@[simp]
theorem unblockedRectangles_self (x : GridState n) : G.unblockedRectangles x x = ∅ := by
  simp [unblockedRectangles]

/-! ### The unblocked complex and its differential -/

/-- The matrix coefficient of the unblocked differential from `x` to `y`: the sum of the weights
of the empty rectangles from `x` to `y` that carry no `X`-marking. -/
noncomputable def unblockedCoefficient (x y : GridState n) : MvPolynomial (Fin n) R :=
  ∑ r ∈ G.unblockedRectangles x y, G.OMonomial R r.toGridRectangle

/-- The matrix coefficient is the sum of the weights of its contributing rectangles. -/
theorem unblockedCoefficient_def (x y : GridState n) :
    G.unblockedCoefficient R x y =
      ∑ r ∈ G.unblockedRectangles x y, G.OMonomial R r.toGridRectangle := by
  rw [unblockedCoefficient]

/-- The unblocked differential has no diagonal matrix coefficient. -/
@[simp]
theorem unblockedCoefficient_self (x : GridState n) : G.unblockedCoefficient R x x = 0 := by
  rw [unblockedCoefficient, unblockedRectangles_self, Finset.sum_empty]

/-- The constant term of a matrix coefficient of the unblocked differential counts those
contributing rectangles that carry no `O`-marking either.

This is the square-centred count obtained by setting every variable to zero. It is not identified
here with the current canonical fully blocked coefficient, whose `GridRectangle.AvoidsMarkings`
predicate still uses the smaller open interior. -/
theorem constantCoeff_unblockedCoefficient (x y : GridState n) :
    constantCoeff (G.unblockedCoefficient R x y) =
      (((G.unblockedRectangles x y).filter fun r =>
        G.OColumns r.toGridRectangle = ∅).card : R) := by
  rw [unblockedCoefficient, map_sum,
    ← Finset.sum_filter_add_sum_filter_not (G.unblockedRectangles x y) fun r =>
      G.OColumns r.toGridRectangle = ∅]
  have h₁ : ∀ r ∈ (G.unblockedRectangles x y).filter
      fun r => G.OColumns r.toGridRectangle = ∅,
      constantCoeff (G.OMonomial R r.toGridRectangle) = 1 := fun r hr => by
    rw [OMonomial, (Finset.mem_filter.mp hr).2, Finset.prod_empty, map_one]
  have h₂ : ∀ r ∈ (G.unblockedRectangles x y).filter
      fun r => ¬G.OColumns r.toGridRectangle = ∅,
      constantCoeff (G.OMonomial R r.toGridRectangle) = 0 := fun r hr => by
    obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hr).2
    rw [OMonomial, map_prod]
    exact Finset.prod_eq_zero hc (by simp)
  rw [Finset.sum_congr rfl h₁, Finset.sum_congr rfl h₂, Finset.sum_const, Finset.sum_const_zero,
    nsmul_eq_mul, mul_one, add_zero]

/-- The value of the unblocked differential on a single grid-state generator. -/
noncomputable def unblockedDifferentialOnGenerator (x : GridState n) :
    GridChainMinus R n :=
  Finset.univ.sum fun y : GridState n => Finsupp.single y (G.unblockedCoefficient R x y)

/-- The `y`-coefficient of the unblocked differential on the generator `x`. -/
@[simp]
theorem unblockedDifferentialOnGenerator_apply (x y : GridState n) :
    G.unblockedDifferentialOnGenerator R x y = G.unblockedCoefficient R x y := by
  rw [unblockedDifferentialOnGenerator, Finsupp.finsetSum_apply, Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz.symm]
  · intro hy
    exact (hy (Finset.mem_univ y)).elim

/-- There is no self-term in the unblocked differential of a generator. -/
theorem unblockedDifferentialOnGenerator_apply_self (x : GridState n) :
    G.unblockedDifferentialOnGenerator R x x = 0 := by
  simp

/-- The unblocked differential of a generator is supported on the column transpositions of that
generator: only a state differing from `x` in exactly two columns, where the two states exchange
rows, can receive a rectangle. -/
theorem unblockedDifferentialOnGenerator_support_subset (x : GridState n) :
    (G.unblockedDifferentialOnGenerator R x).support ⊆ x.columnSwapNeighbors := by
  intro y hy
  rw [Finsupp.mem_support_iff, unblockedDifferentialOnGenerator_apply] at hy
  have hne : (G.unblockedRectangles x y).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [unblockedCoefficient, he, Finset.sum_empty] at hy
    exact hy rfl
  obtain ⟨r, -⟩ := hne
  exact GridState.mem_columnSwapNeighbors.mpr
    ⟨r.left, r.right, r.left_ne_right, r.target_eq_swapColumns⟩

/-- The unblocked grid differential `∂⁻`, as a linear map on `GC⁻` over the polynomial ring. -/
noncomputable def unblockedDifferential :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  Finsupp.lsum (MvPolynomial (Fin n) R) fun x : GridState n =>
    (LinearMap.id :
        MvPolynomial (Fin n) R →ₗ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) R).smulRight
      (G.unblockedDifferentialOnGenerator R x)

/-- The unblocked differential sends a single generator to the corresponding row of weights. -/
@[simp]
theorem unblockedDifferential_single (x : GridState n) :
    G.unblockedDifferential R (Finsupp.single x 1) = G.unblockedDifferentialOnGenerator R x := by
  rw [unblockedDifferential, Finsupp.lsum_single]
  simp

/-- The matrix coefficient of the unblocked differential on a single generator is the sum of the
weights of the contributing rectangles. -/
theorem unblockedDifferential_single_apply (x y : GridState n) :
    G.unblockedDifferential R (Finsupp.single x 1) y = G.unblockedCoefficient R x y := by
  simp

/-- The unblocked differential is the finite sum of its generator rows over the support of a
chain. -/
theorem unblockedDifferential_apply (c : GridChainMinus R n) :
    G.unblockedDifferential R c =
      c.sum fun x a => a • G.unblockedDifferentialOnGenerator R x := by
  rw [unblockedDifferential, Finsupp.lsum_apply]
  simp [Finsupp.sum, LinearMap.smulRight_apply]

/-- The coefficient formula for the unblocked differential on an arbitrary chain. -/
@[simp]
theorem unblockedDifferential_apply_apply (c : GridChainMinus R n) (y : GridState n) :
    G.unblockedDifferential R c y = c.sum fun x a => a * G.unblockedCoefficient R x y := by
  rw [unblockedDifferential_apply]
  simp [Finsupp.sum_apply]

/-! ### The bidegree of the unblocked differential -/

/-- A rectangle counted by the unblocked differential drops the `O`-Maslov grading by one, once
its weight `V^{O(r)}` is charged `-2` per variable.

With `V_c` in Maslov degree `-2`, the term `V^{O(r)} · y` of `∂⁻ x` has Maslov grading
`M_O(x) - 1`: the unblocked differential lowers the Maslov grading by exactly one. -/
theorem maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one
    {x y : GridState n} {r : GridRectangleBetween x y} (hr : r.IsEmpty) :
    G.maslovO y - 2 * ((G.OColumns r.toGridRectangle).card : ℚ) = G.maslovO x - 1 := by
  have h := G.maslovO_sub_maslovO_eq_one_sub_two_mul_card r hr
  rw [G.card_OColumns r.toGridRectangle]
  linarith

/-- A rectangle counted by the unblocked differential preserves the Alexander grading, once its
weight `V^{O(r)}` is charged `-1` per variable.

With `V_c` in Alexander degree `-1`, the term `V^{O(r)} · y` of `∂⁻ x` has Alexander grading
`A(x)`. Unlike the Maslov statement, this uses only that the rectangle carries no
`X`-marking. -/
theorem alexander_sub_card_OColumns_eq_alexander
    {x y : GridState n} {r : GridRectangleBetween x y}
    (hr : Disjoint r.toGridRectangle.coveredSquares G.XSet) :
    G.alexander y - ((G.OColumns r.toGridRectangle).card : ℚ) = G.alexander x := by
  have hX : G.XSet ∩ r.toGridRectangle.coveredSquares = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp hr.symm
  have h := G.alexander_sub_alexander_eq_card_sub_card r
  rw [hX, Finset.card_empty, Nat.cast_zero] at h
  rw [G.card_OColumns r.toGridRectangle]
  linarith

end GridDiagram

end TauCeti
