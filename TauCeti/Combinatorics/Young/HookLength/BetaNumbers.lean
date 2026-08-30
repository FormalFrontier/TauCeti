/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.BetaNumbers
public import TauCeti.Combinatorics.Young.HookLength.Basic

/-!
# Beta-numbers and the hook-length product

Fix a Young diagram `μ` and a bound `r` on its number of rows, and write `βᵢ` for the beta-number
`YoungDiagram.betaNumber μ r i = μ.rowLen i + (r - 1 - i)` of row `i`, defined in
`TauCeti/Combinatorics/Young/BetaNumbers.lean`. For the exact row count `r = μ.colLen 0`, and only
for it, the beta-numbers of the nonempty rows are the hook lengths of the first column: for
`i < μ.colLen 0` the number `βᵢ` is the hook length of the cell `(i, 0)` at the head of row `i`
(`YoungDiagram.betaNumber_eq_hookLength`). A larger bound `r` does not merely append entries to
that list; it raises every beta-number of a nonempty row by the excess `r - μ.colLen 0`, and
contributes the beta-numbers `r - 1 - i` of the empty rows `i`.

The theorem of this file is the identity

`(∏_{c ∈ μ} hookLength μ c) * ∏_{i < j < r} (βᵢ - βⱼ) = ∏_{i < r} βᵢ !`,

`YoungDiagram.prod_hookLength_mul_prod_betaNumber_sub_eq_prod_factorial`. It is the combinatorial
half of the Frame-Robinson-Thrall route to the hook-length formula: the other half is the Frobenius
determinant formula `f^μ · ∏_{i < r} βᵢ ! = μ.card ! · ∏_{i < j < r} (βᵢ - βⱼ)` for the number of
standard Young tableaux, and multiplying the two gives the multiplicative hook-length formula
`f^μ · ∏_{c ∈ μ} hookLength μ c = μ.card !`.

The file also records the one interaction between beta-numbers and corners, which the induction
proving the Frobenius formula runs on: erasing a corner lowers the beta-number of its row by one
and leaves the other beta-numbers alone.

## The row-by-row mechanism

Everything reduces to one statement about a single row `i`, proved in
`YoungDiagram.image_betaNumber_sub_hookLength_union_image_betaNumber`: inside `{0, …, βᵢ - 1}` the
numbers `βᵢ - hookLength μ (i, c)`, for the cells `(i, c)` of row `i`, are exactly the numbers that
are **not** a later beta-number `βⱼ`, `i < j < r`. Equivalently the hook lengths of row `i` are
`{1, …, βᵢ}` with the differences `βᵢ - βⱼ` removed, which is the classical description of a row of
hook lengths.

Two computations drive it. The first, `YoungDiagram.hookLength_add_eq_betaNumber`, is that

`hookLength μ (i, c) + (c + r - μ.colLen c) = βᵢ`,

so the complement `βᵢ - hookLength μ (i, c)` of a hook length in row `i` is `c + r - μ.colLen c`, a
quantity that does not depend on the row at all. The second is that this quantity is never a
beta-number `βⱼ` of an index `j` *within the bound*
(`YoungDiagram.betaNumber_sub_hookLength_ne_betaNumber`, for `j < r`; beyond the bound `βⱼ` is the
unshifted `μ.rowLen j` and the two can agree): the equation `c + r - μ.colLen c = βⱼ` says
`c + j + 1 = μ.colLen c + μ.rowLen j`, which is too large by one when `(j, c) ∈ μ` and too small
when `(j, c) ∉ μ`. Disjointness plus a count of both sides then forces the union to exhaust
`{0, …, βᵢ - 1}`, with no separate surjectivity argument.

## Main results

* `YoungDiagram.hookLength_add_eq_betaNumber`: the complement of a hook length of row `i` inside
  `βᵢ` is `c + r - μ.colLen c`.
* `YoungDiagram.betaNumber_sub_hookLength_ne_betaNumber`: that complement is not a beta-number `βⱼ`
  of an index `j < r`.
* `YoungDiagram.betaNumber_eq_hookLength`: for `r = μ.colLen 0` the beta-numbers of the nonempty
  rows `i < μ.colLen 0` are the hook lengths of the first column.
* `YoungDiagram.image_betaNumber_sub_hookLength_union_image_betaNumber`: the row description of the
  hook lengths.
* `YoungDiagram.prod_hookLength_row_mul_prod_betaNumber_sub_eq_factorial`: the identity for one row.
* `YoungDiagram.prod_hookLength_mul_prod_betaNumber_sub_eq_prod_factorial`: the hook-length
  product identity.
* `YoungDiagram.IsCorner.betaNumber_erase`: erasing a corner lowers exactly one beta-number, by
  one.

## References

* J. S. Frame, G. de B. Robinson, R. M. Thrall, *The hook graphs of the symmetric group*, Canad. J.
  Math. 6 (1954) 316-324, where the identity below is the step from the Frobenius determinant
  formula to the hook-length formula.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I, Section
  1, Example 1, for the description of a row of hook lengths by beta-numbers.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5: the multiplicative hook-length formula.
-/

public section

namespace YoungDiagram

open Finset Nat

variable {μ : YoungDiagram} {r i j c : ℕ}

/-! ### The complement of a hook length in its beta-number -/

/-- Every column of a Young diagram is at most as long as its first column, so the bound `r` on
the number of rows bounds every column length. -/
private theorem colLen_le_of_colLen_zero_le (hr : μ.colLen 0 ≤ r) (c : ℕ) : μ.colLen c ≤ r :=
  (μ.colLen_anti 0 c (Nat.zero_le c)).trans hr

/-- A row bound for the whole diagram bounds the index of any row that reaches column `c`. -/
private theorem lt_of_lt_rowLen (hr : μ.colLen 0 ≤ r) (hc : c < μ.rowLen i) : i < r :=
  (mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr hc)).trans_le (colLen_le_of_colLen_zero_le hr c)

/-- **The complement of a hook length inside its beta-number.** For a cell `(i, c)` of `μ` whose
column is no longer than `r`, the hook length of `(i, c)` and the quantity `c + r - μ.colLen c` add
up to the beta-number of row `i`. The second summand depends only on the column `c`, which is what
makes the beta-number description of a row of hook lengths uniform in the row. -/
theorem hookLength_add_eq_betaNumber (hr : μ.colLen c ≤ r) (hc : c < μ.rowLen i) :
    μ.hookLength (i, c) + (c + r - μ.colLen c) = μ.betaNumber r i := by
  have hcol : i < μ.colLen c := mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr hc)
  simp only [hookLength_def, armLength_def, legLength_def, betaNumber_def]
  omega

/-- A hook length of row `i` is at most the beta-number of row `i`. -/
theorem hookLength_le_betaNumber (hr : μ.colLen c ≤ r) (hc : c < μ.rowLen i) :
    μ.hookLength (i, c) ≤ μ.betaNumber r i :=
  Nat.le.intro (hookLength_add_eq_betaNumber hr hc)

/-- The complement of a hook length of row `i` inside its beta-number, in the closed form supplied
by `YoungDiagram.hookLength_add_eq_betaNumber`. -/
@[simp]
theorem betaNumber_sub_hookLength (hi : i < r) (hc : c < μ.rowLen i) :
    μ.betaNumber r i - μ.hookLength (i, c) = c + r - μ.colLen c := by
  have hcol : i < μ.colLen c := mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr hc)
  simp only [hookLength_def, armLength_def, legLength_def, betaNumber_def]
  omega

/-- **The complements of the hook lengths of a row avoid the beta-numbers inside the bound.** By
`YoungDiagram.betaNumber_sub_hookLength` the claim is that `c + r - μ.colLen c` is never a
beta-number `βⱼ` with `j < r`, that is, that `c + j + 1 = μ.colLen c + μ.rowLen j` is impossible:
the right-hand side is at least `c + j + 2` when the cell `(j, c)` lies in `μ` and at most `c + j`
when it does not. -/
theorem betaNumber_sub_hookLength_ne_betaNumber (hi : i < r) (hc : c < μ.rowLen i) (hj : j < r) :
    μ.betaNumber r i - μ.hookLength (i, c) ≠ μ.betaNumber r j := by
  rw [betaNumber_sub_hookLength hi hc]
  simp only [betaNumber_def]
  by_cases hm : (j, c) ∈ μ
  · have h1 : j < μ.colLen c := mem_iff_lt_colLen.mp hm
    have h2 : c < μ.rowLen j := mem_iff_lt_rowLen.mp hm
    omega
  · have h1 : μ.colLen c ≤ j := Nat.not_lt.mp fun h => hm (mem_iff_lt_colLen.mpr h)
    have h2 : μ.rowLen j ≤ c := Nat.not_lt.mp fun h => hm (mem_iff_lt_rowLen.mpr h)
    omega

/-! ### Beta-numbers as hook lengths -/

/-- Relative to the exact number of rows, the beta-numbers of the nonempty rows of a Young diagram
are the hook lengths of its first column: the `c = 0`, `r = μ.colLen 0` case of
`YoungDiagram.hookLength_add_eq_betaNumber`, where the complement `c + r - μ.colLen c` vanishes. -/
@[simp]
theorem betaNumber_eq_hookLength (hi : i < μ.colLen 0) :
    μ.betaNumber (μ.colLen 0) i = μ.hookLength (i, 0) := by
  have hrow : 0 < μ.rowLen i := mem_iff_lt_rowLen.mp (mem_iff_lt_colLen.mpr hi)
  have := hookLength_add_eq_betaNumber (μ := μ) (c := 0) (r := μ.colLen 0) le_rfl hrow
  omega

/-! ### A row of hook lengths -/

/-- The complements of the hook lengths of a row increase strictly, because the hook lengths of a
row strictly decrease (`YoungDiagram.hookLength_lt_hookLength_of_col_lt`) and are bounded by the
beta-number of that row. -/
private theorem strictMonoOn_betaNumber_sub_hookLength (hr : μ.colLen 0 ≤ r) :
    StrictMonoOn (fun c => μ.betaNumber r i - μ.hookLength (i, c)) ↑(range (μ.rowLen i)) := by
  intro a ha b hb hab
  simp only [coe_range, Set.mem_Iio] at ha hb
  have hla := hookLength_le_betaNumber (colLen_le_of_colLen_zero_le hr a) ha
  have hlb := hookLength_le_betaNumber (colLen_le_of_colLen_zero_le hr b) hb
  have := μ.hookLength_lt_hookLength_of_col_lt (mem_iff_lt_rowLen.mpr hb) hab
  simp only
  omega

/-- The beta-numbers of the rows strictly below `i` and inside the bound are distinct; the special
case of `YoungDiagram.injOn_betaNumber` used to count and to reindex products over them. -/
private theorem injOn_betaNumber_Ico (μ : YoungDiagram) (r i : ℕ) :
    Set.InjOn (μ.betaNumber r) ↑(Ico (i + 1) r) :=
  (μ.injOn_betaNumber r).mono fun j hj => by
    simp only [coe_Ico, Set.mem_Ico] at hj
    exact Set.mem_Iio.mpr hj.2

/-- The complements of the hook lengths of row `i` and the later beta-numbers are disjoint, by
`YoungDiagram.betaNumber_sub_hookLength_ne_betaNumber`. -/
private theorem disjoint_image_betaNumber_sub_hookLength (hr : μ.colLen 0 ≤ r) :
    Disjoint ((range (μ.rowLen i)).image fun c => μ.betaNumber r i - μ.hookLength (i, c))
      ((Ico (i + 1) r).image (μ.betaNumber r)) := by
  simp only [disjoint_left, mem_image, mem_range, mem_Ico]
  rintro m ⟨c, hc, rfl⟩ ⟨j, ⟨-, hj⟩, hmj⟩
  exact betaNumber_sub_hookLength_ne_betaNumber (lt_of_lt_rowLen hr hc) hc hj hmj.symm

/-- **The hook lengths of a single row, through beta-numbers.** The complements
`βᵢ - hookLength μ (i, c)` of the hook lengths of row `i`, together with the later beta-numbers
`βⱼ` for `i < j < r`, partition `{0, …, βᵢ - 1}`.

Both families lie in `{0, …, βᵢ - 1}` and are disjoint, and they have `μ.rowLen i` and `r - 1 - i`
members respectively, which is exactly `βᵢ` in total; so the inclusion is an equality. -/
theorem image_betaNumber_sub_hookLength_union_image_betaNumber (hr : μ.colLen 0 ≤ r) :
    ((range (μ.rowLen i)).image fun c => μ.betaNumber r i - μ.hookLength (i, c)) ∪
        ((Ico (i + 1) r).image (μ.betaNumber r)) = range (μ.betaNumber r i) := by
  refine eq_of_subset_of_card_le ?_ ?_
  · intro m hm
    rcases mem_union.mp hm with hm | hm
    · obtain ⟨c, hc, rfl⟩ := mem_image.mp hm
      have hc' : c < μ.rowLen i := mem_range.mp hc
      have := hookLength_add_eq_betaNumber (colLen_le_of_colLen_zero_le hr c) hc'
      have := μ.hookLength_pos (c := (i, c))
      exact mem_range.mpr (by omega)
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
      obtain ⟨hj₁, hj₂⟩ := mem_Ico.mp hj
      exact mem_range.mpr (μ.betaNumber_lt_betaNumber hj₁ hj₂)
  · rw [card_union_of_disjoint (disjoint_image_betaNumber_sub_hookLength hr),
      card_image_of_injOn (strictMonoOn_betaNumber_sub_hookLength hr).injOn,
      card_image_of_injOn (μ.injOn_betaNumber_Ico r i),
      card_range, card_range, Nat.card_Ico, betaNumber_def]
    omega

/-- **The hook-length product identity for a single row.** The hook lengths of row `i`, multiplied
by the differences `βᵢ - βⱼ` between its beta-number and the later ones, give `βᵢ !`. -/
theorem prod_hookLength_row_mul_prod_betaNumber_sub_eq_factorial (hr : μ.colLen 0 ≤ r) :
    ((∏ c ∈ range (μ.rowLen i), μ.hookLength (i, c)) *
        ∏ j ∈ Ico (i + 1) r, (μ.betaNumber r i - μ.betaNumber r j))
      = (μ.betaNumber r i) ! := by
  -- the descending product `∏_{m < L} (L - m)` is `L !`
  have hfact : ∏ m ∈ range (μ.betaNumber r i), (μ.betaNumber r i - m) = (μ.betaNumber r i) ! := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  rw [← hfact, ← image_betaNumber_sub_hookLength_union_image_betaNumber hr,
    prod_union (disjoint_image_betaNumber_sub_hookLength hr),
    prod_image (strictMonoOn_betaNumber_sub_hookLength hr).injOn,
    prod_image (μ.injOn_betaNumber_Ico r i)]
  refine congrArg₂ (· * ·) (prod_congr rfl fun c hc => ?_) rfl
  have hc' : c < μ.rowLen i := mem_range.mp hc
  have := hookLength_add_eq_betaNumber (colLen_le_of_colLen_zero_le hr c) hc'
  omega

/-! ### The hook-length product -/

/-- A product over the cells of a diagram with at most `r` rows, read row by row: the cells are
fibred over their row index by `Prod.fst`, and the fibre of `i` is the row `μ.row i`. -/
private theorem prod_cells_eq_prod_range {M : Type*} [CommMonoid M] (hr : μ.colLen 0 ≤ r)
    (f : ℕ × ℕ → M) :
    ∏ c ∈ μ.cells, f c = ∏ i ∈ range r, ∏ c ∈ range (μ.rowLen i), f (i, c) := by
  have hmaps : ∀ c ∈ μ.cells, c.1 ∈ range r := by
    rintro ⟨a, b⟩ hc
    exact mem_range.mpr
      ((mem_iff_lt_colLen.mp ((mem_cells _).mp hc)).trans_le (colLen_le_of_colLen_zero_le hr b))
  rw [← prod_fiberwise_of_maps_to hmaps f]
  refine prod_congr rfl fun i _ => ?_
  -- the fibre of `i` is `YoungDiagram.row`, defined as exactly this filter
  rw [← row, row_eq_prod, Finset.prod_product, prod_singleton]

/-- **The hook-length product identity.** For a Young diagram `μ` with at most `r` rows, the
product of all its hook lengths, multiplied by the Vandermonde-style product of the differences of
its beta-numbers, is the product of the factorials of its beta-numbers.

Combined with the Frobenius determinant formula
`f^μ · ∏_{i < r} βᵢ ! = μ.card ! · ∏_{i < j < r} (βᵢ - βⱼ)` for the number of standard Young
tableaux, this gives the multiplicative hook-length formula. -/
theorem prod_hookLength_mul_prod_betaNumber_sub_eq_prod_factorial (μ : YoungDiagram)
    (hr : μ.colLen 0 ≤ r) :
    ((∏ c ∈ μ.cells, μ.hookLength c) *
        ∏ i ∈ range r, ∏ j ∈ Ico (i + 1) r, (μ.betaNumber r i - μ.betaNumber r j))
      = ∏ i ∈ range r, (μ.betaNumber r i) ! := by
  rw [prod_cells_eq_prod_range hr, ← prod_mul_distrib]
  exact prod_congr rfl fun i _ => prod_hookLength_row_mul_prod_betaNumber_sub_eq_factorial hr

/-! ### Erasing a corner -/

/-- Erasing a corner lowers the beta-number of its row by one and leaves the other beta-numbers
unchanged. -/
@[simp]
theorem IsCorner.betaNumber_erase {c : ℕ × ℕ} (h : IsCorner μ c) (r i : ℕ) :
    (μ.erase c).betaNumber r i
      = if c.1 = i then μ.betaNumber r i - 1 else μ.betaNumber r i := by
  have hrow : 0 < μ.rowLen c.1 := by rw [h.rowLen_eq_snd_add_one]; omega
  rw [betaNumber_def, h.rowLen_erase, betaNumber_def]
  split_ifs with hi
  · subst hi; omega
  · rfl

end YoungDiagram
