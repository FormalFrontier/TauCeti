/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import TauCeti.KnotTheory.Grid.Complex
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import TauCeti.KnotTheory.Grid.Rectangle.Count
import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# The minus grid differential

This file defines the polynomial-valued differential underlying the minus version of grid
homology. Its coefficient ring is `ZMod 2[V₁, ..., Vₙ]`, represented as
`MvPolynomial (Fin n) (ZMod 2)`. An empty rectangle contributes when its interior avoids every
`X` marking, with weight the product of the variables indexed by the `O` markings in its
interior.

Taking the constant coefficient sets every variable to zero. The resulting rectangle coefficient
is exactly the fully blocked coefficient already defined in `BlockedRectangle.lean`: precisely the
rectangles containing no `O` marking survive, while the minus condition already excludes every
`X` marking. This gives a direct consistency check between the two grid differentials.

The square-zero theorem is not asserted here. Until the rectangle-decomposition argument is
available, `minusDifferential` is a linear endomorphism rather than a packaged chain complex.

## Main definitions

* `TauCeti.GridMinusRing`: the polynomial coefficient ring `ZMod 2[V₁, ..., Vₙ]`.
* `TauCeti.GridRectangleBetween.interiorOColumns`: the column labels of the `O` markings in a
  rectangle interior.
* `TauCeti.GridRectangleBetween.minusRectangleWeight`: the corresponding variable monomial.
* `TauCeti.GridDiagram.minusRectangles`: empty rectangles avoiding all `X` markings.
* `TauCeti.GridDiagram.minusRectangleCoefficient`: their weighted sum.
* `TauCeti.GridDiagram.minusDifferential`: the resulting polynomial-linear endomorphism of grid
  chains.

## Main result

* `TauCeti.GridDiagram.constantCoeff_minusRectangleCoefficient`: setting every variable to zero
  recovers the fully blocked rectangle coefficient.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, which asks for the
unblocked complex `GC⁻` over `𝔽₂[V₁, ..., Vₙ]`. The definition follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.
-/

public section

namespace TauCeti

/-- The coefficient ring for the minus grid differential on an `n × n` grid. Its variable indexed
by `i : Fin n` records an `O` marking in column `i`. -/
abbrev GridMinusRing (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n} (R : GridRectangleBetween x y)

/-- The column labels of the `O` markings in the interior of an oriented grid rectangle.

There is one `O` marking in every column, so its column is also its variable label in
`GridMinusRing n`. -/
noncomputable def interiorOColumns (G : GridDiagram n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (i, G.O i) ∈ R.toGridRectangle.interior

/-- A column labels an interior `O` marking exactly when its `O` marking lies in the rectangle
interior. -/
@[simp]
theorem mem_interiorOColumns (G : GridDiagram n) (i : Fin n) :
    i ∈ R.interiorOColumns G ↔ (i, G.O i) ∈ R.toGridRectangle.interior := by
  classical
  simp [interiorOColumns]

/-- A rectangle contains no interior `O` marking exactly when its interior is disjoint from the
diagram's `O`-marking set. -/
theorem interiorOColumns_eq_empty_iff (G : GridDiagram n) :
    R.interiorOColumns G = ∅ ↔ Disjoint R.toGridRectangle.interior G.OSet := by
  classical
  rw [interiorOColumns, Finset.filter_eq_empty_iff, Finset.disjoint_left]
  constructor
  · intro hfilter p hpR hpO
    have hrow : G.O p.1 = p.2 := (G.mem_OSet p).mp hpO
    exact hfilter (x := p.1) (Finset.mem_univ _) (hrow.symm ▸ hpR)
  · intro hdisjoint i _ hi
    apply hdisjoint hi
    simp

/-- The monomial contributed by a rectangle to the minus differential: one variable for every
`O` marking in its interior. -/
noncomputable def minusRectangleWeight (G : GridDiagram n) : GridMinusRing n :=
  ∏ i ∈ R.interiorOColumns G, MvPolynomial.X i

/-- The minus rectangle weight is the product of the variables labeling its interior `O`
markings. -/
theorem minusRectangleWeight_def (G : GridDiagram n) :
    R.minusRectangleWeight G = ∏ i ∈ R.interiorOColumns G, MvPolynomial.X i :=
  (rfl)

/-- The constant coefficient of a minus rectangle weight is one exactly when the rectangle has
no interior `O` marking. -/
@[simp]
theorem constantCoeff_minusRectangleWeight (G : GridDiagram n) :
    MvPolynomial.constantCoeff (R.minusRectangleWeight G) =
      if R.interiorOColumns G = ∅ then 1 else 0 := by
  classical
  by_cases h : R.interiorOColumns G = ∅
  · simp [minusRectangleWeight, h]
  · have hcard : 0 < (R.interiorOColumns G).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)
    simp [minusRectangleWeight, h, zero_pow (ne_of_gt hcard)]

end GridRectangleBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (x y : GridState n)

/-- The finite set of empty rectangles from `x` to `y` whose interiors avoid every `X` marking.

Unlike a fully blocked rectangle, a minus rectangle may contain `O` markings; those markings
determine its polynomial weight. -/
noncomputable def minusRectangles : Finset (GridRectangleBetween x y) := by
  classical
  exact (GridRectangleBetween.emptyRectangles x y).filter fun R =>
    Disjoint R.toGridRectangle.interior G.XSet

/-- Membership in the minus rectangle set is emptiness together with avoidance of every `X`
marking. -/
@[simp]
theorem mem_minusRectangles (R : GridRectangleBetween x y) :
    R ∈ G.minusRectangles x y ↔
      R.IsEmpty ∧ Disjoint R.toGridRectangle.interior G.XSet := by
  classical
  simp [minusRectangles]

/-- Every minus rectangle is an empty rectangle between the same states. -/
theorem minusRectangles_subset_emptyRectangles :
    G.minusRectangles x y ⊆ GridRectangleBetween.emptyRectangles x y := by
  classical
  intro R hR
  exact (GridRectangleBetween.mem_emptyRectangles R).mpr
    ((G.mem_minusRectangles x y R).mp hR).1

/-- There are at most two minus rectangles in each matrix coefficient of the minus differential. -/
theorem card_minusRectangles_le_two : (G.minusRectangles x y).card ≤ 2 :=
  GridRectangleBetween.card_le_two (G.minusRectangles x y)

/-- The set of minus rectangles from a grid state to itself is empty. -/
@[simp]
theorem minusRectangles_self (x : GridState n) : G.minusRectangles x x = ∅ := by
  classical
  simp [minusRectangles]

/-- Fully blocked rectangles are exactly the minus rectangles with no interior `O` marking. -/
theorem fullyBlockedRectangles_eq_filter_minusRectangles :
    G.fullyBlockedRectangles x y =
      (G.minusRectangles x y).filter fun R => R.interiorOColumns G = ∅ := by
  classical
  ext R
  rw [G.mem_fullyBlockedRectangles x y R, Finset.mem_filter, G.mem_minusRectangles x y R,
    R.interiorOColumns_eq_empty_iff G, R.avoidsMarkings_iff G]
  tauto

/-- The coefficient from `x` to `y` in the minus grid differential: the sum of the monomial
weights of all empty rectangles avoiding the `X` markings. -/
noncomputable def minusRectangleCoefficient : GridMinusRing n :=
  ∑ R ∈ G.minusRectangles x y, R.minusRectangleWeight G

/-- The minus rectangle coefficient is the finite weighted sum over `minusRectangles`. -/
theorem minusRectangleCoefficient_def :
    G.minusRectangleCoefficient x y =
      ∑ R ∈ G.minusRectangles x y, R.minusRectangleWeight G :=
  (rfl)

/-- The minus rectangle coefficient from a grid state to itself is zero. -/
@[simp]
theorem minusRectangleCoefficient_self (x : GridState n) :
    G.minusRectangleCoefficient x x = 0 := by
  simp [minusRectangleCoefficient]

/-- A nonzero minus rectangle coefficient forces the target state to be a column transposition of
the source state. -/
theorem exists_swapColumns_of_minusRectangleCoefficient_ne_zero
    (h : G.minusRectangleCoefficient x y ≠ 0) :
    ∃ a b : Fin n, a ≠ b ∧ y = x.swapColumns a b := by
  have hrect : (G.minusRectangles x y).Nonempty := by
    by_contra hempty
    rw [minusRectangleCoefficient_def, Finset.not_nonempty_iff_eq_empty.mp hempty] at h
    simp at h
  obtain ⟨R, hR⟩ := hrect
  exact ⟨R.left, R.right, R.left_ne_right, R.target_eq_swapColumns⟩

/-- Setting every variable to zero in a minus rectangle coefficient recovers the fully blocked
rectangle coefficient. -/
@[simp]
theorem constantCoeff_minusRectangleCoefficient :
    MvPolynomial.constantCoeff (G.minusRectangleCoefficient x y) =
      G.fullyBlockedRectangleCount x y := by
  classical
  simp only [minusRectangleCoefficient, map_sum,
    GridRectangleBetween.constantCoeff_minusRectangleWeight]
  rw [Finset.sum_boole, ← G.fullyBlockedRectangles_eq_filter_minusRectangles x y,
    G.fullyBlockedRectangleCount_def x y]

/-- The value of the minus differential on one grid-state generator. -/
noncomputable def minusDifferentialOnGenerator (x : GridState n) : GridChain (GridMinusRing n) n :=
  Finsupp.equivFunOnFinite.symm fun y => G.minusRectangleCoefficient x y

/-- The generator row of the minus differential is the finitely supported function of weighted
rectangle coefficients. -/
theorem minusDifferentialOnGenerator_def (x : GridState n) :
    G.minusDifferentialOnGenerator x =
      Finsupp.equivFunOnFinite.symm fun y => G.minusRectangleCoefficient x y :=
  by simp only [minusDifferentialOnGenerator]

/-- The `y`-coefficient of the minus differential on the generator `x`. -/
@[simp]
theorem minusDifferentialOnGenerator_apply (x y : GridState n) :
    G.minusDifferentialOnGenerator x y = G.minusRectangleCoefficient x y := by
  rw [minusDifferentialOnGenerator_def]
  exact congrFun (Finsupp.coe_equivFunOnFinite_symm _) y

/-- There is no self-term in the minus differential of a generator. -/
theorem minusDifferentialOnGenerator_apply_self (x : GridState n) :
    G.minusDifferentialOnGenerator x x = 0 := by
  simp

/-- The minus differential of a generator is supported on its column transpositions. -/
theorem exists_swapColumns_of_minusDifferentialOnGenerator_ne_zero {x y : GridState n}
    (h : G.minusDifferentialOnGenerator x y ≠ 0) :
    ∃ a b : Fin n, a ≠ b ∧ y = x.swapColumns a b := by
  rw [minusDifferentialOnGenerator_apply] at h
  exact G.exists_swapColumns_of_minusRectangleCoefficient_ne_zero x y h

/-- The minus grid differential as a polynomial-linear endomorphism of the free module on grid
states. -/
noncomputable def minusDifferential :
    GridChain (GridMinusRing n) n →ₗ[GridMinusRing n] GridChain (GridMinusRing n) n :=
  Finsupp.linearCombination (GridMinusRing n) G.minusDifferentialOnGenerator

/-- The minus differential sends a basis generator to its rectangle-coefficient row. -/
@[simp]
theorem minusDifferential_single (x : GridState n) :
    G.minusDifferential (Finsupp.single x 1) = G.minusDifferentialOnGenerator x := by
  classical
  rw [minusDifferential, Finsupp.linearCombination_single]
  simp

/-- The matrix coefficient of the minus differential on a basis generator is the weighted
minus rectangle coefficient. -/
theorem minusDifferential_single_apply (x y : GridState n) :
    G.minusDifferential (Finsupp.single x 1) y = G.minusRectangleCoefficient x y := by
  simp

/-- The self-coefficient of the minus differential on a single generator is zero. -/
theorem minusDifferential_single_apply_self (x : GridState n) :
    G.minusDifferential (Finsupp.single x 1) x = 0 := by
  simp

/-- Taking the constant coefficient of a matrix entry of the minus differential gives the
corresponding matrix entry of the fully blocked differential. -/
theorem constantCoeff_minusDifferential_single_apply (x y : GridState n) :
    MvPolynomial.constantCoeff (G.minusDifferential (Finsupp.single x 1) y) =
      G.fullyBlockedDifferential (Finsupp.single x 1) y := by
  simp

/-- The minus differential is the finite sum of its generator rows over the support of a chain. -/
theorem minusDifferential_apply (c : GridChain (GridMinusRing n) n) :
    G.minusDifferential c =
      c.sum fun x a => a • G.minusDifferentialOnGenerator x := by
  rw [minusDifferential, Finsupp.linearCombination_apply]

/-- The coefficient formula for the minus differential on an arbitrary polynomial grid chain. -/
@[simp]
theorem minusDifferential_apply_apply (c : GridChain (GridMinusRing n) n) (y : GridState n) :
    G.minusDifferential c y =
      c.sum fun x a => a * G.minusRectangleCoefficient x y := by
  classical
  rw [minusDifferential_apply]
  simp [Finsupp.sum_apply]

end GridDiagram

end TauCeti
