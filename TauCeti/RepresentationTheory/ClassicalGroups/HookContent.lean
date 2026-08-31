/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.HookLength.BetaNumbers
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylDimension

public section

/-!
# The hook-content formula

`TauCeti.weylDimension` is the value `∏_{i < j} (λᵢ - λⱼ + j - i) / (j - i)` of the Weyl dimension
formula for `GL n`, a product over the pairs of *rows*.  For a polynomial weight — a Young diagram
`μ` with at most `n` rows, read as a weight by `TauCeti.weightOfShape` — the same number is a
product over the *cells* of `μ`,

`weylDimension (weightOfShape n μ) = ∏_{(i, j) ∈ μ} (n + j - i) / hookLength μ (i, j)`,

the **hook-content formula**: each cell contributes the quotient of `n` plus its content `j - i` by
its hook length.  This file proves it, in the division-free form
`TauCeti.weylDimension_weightOfShape_mul_prod_hookLength` and in the quotient form
`TauCeti.weylDimension_weightOfShape_eq_prod_div`, and extends it to an arbitrary dominant weight
through the determinant twist (`TauCeti.weylDimension_eq_prod_detShiftShape_div_hookLength`).

## The route

Both sides are compared against the beta-numbers `βᵢ = μ.rowLen i + (n - 1 - i)` of
`TauCeti/Combinatorics/Young/BetaNumbers.lean`, which are the row lengths of `μ` shifted so as to
be strictly decreasing.  Three identities meet.

* The hook lengths, by `YoungDiagram.prod_hookLength_mul_prod_betaNumber_sub_eq_prod_factorial`:
  `(∏_{c ∈ μ} hookLength c) · ∏_{i < j < n} (βᵢ - βⱼ) = ∏_{i < n} βᵢ !`.
* The contents, proved here: row `i` contributes the cells `(i, 0), …, (i, μ.rowLen i - 1)`, whose
  contents `n + j - i` are the `μ.rowLen i` consecutive integers starting at `n - i`, so that row
  contributes `βᵢ ! / (n - 1 - i)!` — and the missing factorials multiply to the superfactorial
  `sf (n - 1)`.  This is `∏_{c ∈ μ} (n + c₂ - c₁) · sf (n - 1) = ∏_{i < n} βᵢ !`.
* The Weyl dimension, by `TauCeti.weylDimension_mul_superFactorial`:
  `weylDimension · sf (n - 1) = ∏_{i < j < n} (βᵢ - βⱼ)`, once the numerator of the Weyl dimension
  formula is recognized as the Vandermonde-style product of the beta-numbers.  That recognition is
  the identity `βᵢ - βⱼ = (λᵢ - i) - (λⱼ - j)`: the two shifts differ by the constant `n - 1`.

Cancelling the (positive) superfactorial from
`(∏ contents) · sf = ∏ βᵢ ! = (∏ hooks) · ∏ (βᵢ - βⱼ) = (∏ hooks) · weylDimension · sf`
leaves the formula.

## Main results

* `TauCeti.weylDimension_weightOfShape_mul_prod_hookLength`: **the hook-content formula**, in
  division-free form over `ℕ`.
* `TauCeti.weylDimension_weightOfShape_eq_prod_div`: its quotient form over `ℚ`.
* `TauCeti.weylDimension_eq_prod_detShiftShape_div_hookLength`: the quotient form for an arbitrary
  dominant weight, whose cells are those of its polynomial part
  `TauCeti.DominantWeight.detShiftShape`.  The Weyl dimension is unchanged by a determinant twist,
  and so is each factor, the content and the hook length being read off the same diagram.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 5, "The Weyl dimension formula", which asks for the hook-content form of
  `TauCeti.weylDimension` and for the proof that the two agree.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Theorem 6.3 and
  Exercise 6.4, where the hook-content formula is stated for `GL n`.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3, Example 4.
-/

namespace TauCeti

-- `_root_.Nat` rather than `Nat`: inside `namespace TauCeti` the latter is ambiguous, `TauCeti.Nat`
-- being a namespace of this repository too.
open Finset _root_.Nat

variable {n i : ℕ} {μ : YoungDiagram}

/-! ### The product of the contents -/

/-- The cells of row `i` of `μ` have contents `n + j - i` running over the `μ.rowLen i` consecutive
integers starting at `n - i`, so their product completes `(n - 1 - i)!` to `βᵢ !`. -/
private theorem factorial_mul_prod_range_rowLen (μ : YoungDiagram) (h : i < n) :
    (n - 1 - i)! * ∏ j ∈ range (μ.rowLen i), (n - i + j) = (μ.betaNumber n i)! := by
  have hshift : n - i = (n - 1 - i) + 1 := by omega
  rw [← Nat.ascFactorial_eq_prod_range, hshift, Nat.factorial_mul_ascFactorial,
    YoungDiagram.betaNumber_def, Nat.add_comm]

/-- The factorials left over by `TauCeti.factorial_mul_prod_range_rowLen` are `0!, 1!, …, (n-1)!`,
whose product is the superfactorial. -/
private theorem prod_range_factorial_sub (n : ℕ) :
    ∏ i ∈ range n, (n - 1 - i)! = (n - 1).superFactorial := by
  rw [Finset.prod_range_reflect (fun i => i !) n]
  cases n with
  | zero => simp
  | succ m => exact Nat.prod_range_succ_factorial m

/-- **The content product.** For a Young diagram with at most `n` rows, the product of the contents
`n + j - i` of its cells, times the superfactorial `sf (n - 1)`, is the product of the factorials of
its beta-numbers. -/
private theorem prod_cells_mul_superFactorial (hμ : μ.colLen 0 ≤ n) :
    (∏ c ∈ μ.cells, (n + c.2 - c.1)) * (n - 1).superFactorial
      = ∏ i ∈ range n, (μ.betaNumber n i)! := by
  rw [YoungDiagram.prod_cells_eq_prod_range μ hμ, ← prod_range_factorial_sub n,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.mp hi
  have hcontent : ∏ j ∈ range (μ.rowLen i), (n + j - i) = ∏ j ∈ range (μ.rowLen i), (n - i + j) :=
    Finset.prod_congr rfl fun j _ => by omega
  rw [hcontent, mul_comm]
  exact factorial_mul_prod_range_rowLen μ hi'

/-! ### The numerator of the Weyl dimension formula -/

/-- **The Weyl numerator in beta-numbers.** The differences of the beta-numbers of `μ` are the
differences of the shifted row lengths `λᵢ - i`, the two shifts differing by the constant `n - 1`,
so the Vandermonde-style product of the former is the numerator of the Weyl dimension formula at
the weight `μ` determines. -/
private theorem prod_betaNumber_sub_eq_weylDimensionNumerator (n : ℕ) (μ : YoungDiagram) :
    (∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n,
        ((μ.betaNumber n i : ℤ) - (μ.betaNumber n j : ℤ)))
      = weylDimensionNumerator (weightOfShape n μ) := by
  rw [weylDimensionNumerator_eq_prod_prod,
    ← Fin.prod_univ_eq_prod_range
      (fun i => ∏ j ∈ Ico (i + 1) n,
        ((μ.betaNumber n i : ℤ) - (μ.betaNumber n j : ℤ))) n]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hIco : Finset.Ico ((i : ℕ) + 1) n = Finset.Ioo (i : ℕ) n := by
    ext j; simp only [Finset.mem_Ico, Finset.mem_Ioo]; omega
  rw [hIco, ← Fin.map_valEmbedding_Ioi, Finset.prod_map]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hij : (i : ℕ) < (j : ℕ) := Fin.lt_def.mp (Finset.mem_Ioi.mp hj)
  have hjn : (j : ℕ) < n := j.isLt
  have hrow : μ.rowLen j ≤ μ.rowLen i := μ.rowLen_anti _ _ hij.le
  simp only [Fin.valEmbedding_apply, YoungDiagram.betaNumber_def, weightOfShape_apply]
  omega

/-! ### The hook-content formula -/

/-- **The hook-content formula**, in division-free form: for a Young diagram `μ` with at most `n`
rows, the Weyl dimension of the weight it determines, times the product of the hook lengths of `μ`,
is the product over the cells of `μ` of `n` plus the content `j - i`. -/
theorem weylDimension_weightOfShape_mul_prod_hookLength (hμ : μ.colLen 0 ≤ n) :
    weylDimension (weightOfShape n μ) * ∏ c ∈ μ.cells, μ.hookLength c
      = ∏ c ∈ μ.cells, (n + c.2 - c.1) := by
  have hnum : weylDimension (weightOfShape n μ) * (n - 1).superFactorial
      = ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, (μ.betaNumber n i - μ.betaNumber n j) := by
    have := (weylDimension_mul_superFactorial (weightOfShape n μ)).trans
      ((YoungDiagram.cast_prod_betaNumber_sub μ n).trans
        (prod_betaNumber_sub_eq_weylDimensionNumerator n μ)).symm
    exact_mod_cast this
  have hsf : 0 < (n - 1).superFactorial := Nat.superFactorial_pos (n - 1)
  refine Nat.eq_of_mul_eq_mul_right hsf ?_
  calc weylDimension (weightOfShape n μ) * (∏ c ∈ μ.cells, μ.hookLength c)
        * (n - 1).superFactorial
      = (∏ c ∈ μ.cells, μ.hookLength c)
          * (weylDimension (weightOfShape n μ) * (n - 1).superFactorial) := by ring
    _ = (∏ c ∈ μ.cells, μ.hookLength c)
          * ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, (μ.betaNumber n i - μ.betaNumber n j) := by
        rw [hnum]
    _ = ∏ i ∈ range n, (μ.betaNumber n i)! :=
        YoungDiagram.prod_hookLength_mul_prod_betaNumber_sub_eq_prod_factorial μ hμ
    _ = (∏ c ∈ μ.cells, (n + c.2 - c.1)) * (n - 1).superFactorial :=
        (prod_cells_mul_superFactorial hμ).symm

/-- **The hook-content formula**, in its quotient form over `ℚ`: for a Young diagram `μ` with at
most `n` rows, the Weyl dimension of the weight it determines is the product over the cells of `μ`
of `(n + j - i) / hookLength μ (i, j)`. -/
theorem weylDimension_weightOfShape_eq_prod_div (hμ : μ.colLen 0 ≤ n) :
    (weylDimension (weightOfShape n μ) : ℚ)
      = ∏ c ∈ μ.cells, (((n : ℚ) + c.2 - c.1) / μ.hookLength c) := by
  have hhook : (∏ c ∈ μ.cells, (μ.hookLength c : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun c _ => by
      exact_mod_cast (μ.hookLength_pos c).ne'
  rw [Finset.prod_div_distrib, eq_div_iff hhook, ← Nat.cast_prod, ← Nat.cast_mul,
    weylDimension_weightOfShape_mul_prod_hookLength hμ, Nat.cast_prod]
  refine Finset.prod_congr rfl fun c hc => ?_
  have hc' : c.1 < n :=
    ((YoungDiagram.mem_iff_lt_colLen.mp ((YoungDiagram.mem_cells c).mp hc)).trans_le
      ((μ.colLen_anti 0 c.2 c.2.zero_le).trans hμ))
  have : c.1 ≤ n + c.2 := by omega
  push_cast [Nat.cast_sub this]
  ring

/-- **The hook-content formula for an arbitrary dominant weight.** Every dominant weight of `GL n`
is a determinant twist of a polynomial one, whose Young diagram is
`TauCeti.DominantWeight.detShiftShape`; the twist changes neither the Weyl dimension nor the
diagram, so the hook-content formula holds for every weight, read on that diagram. -/
theorem weylDimension_eq_prod_detShiftShape_div_hookLength (l : DominantWeight n) :
    (weylDimension l : ℚ)
      = ∏ c ∈ l.detShiftShape.cells,
          (((n : ℚ) + c.2 - c.1) / l.detShiftShape.hookLength c) := by
  rw [← weylDimension_weightOfShape_eq_prod_div l.colLen_zero_detShiftShape_le,
    DominantWeight.weightOfShape_detShiftShape, weylDimension_shift]

end TauCeti
