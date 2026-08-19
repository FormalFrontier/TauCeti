/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic

public section

/-!
# The Schur polynomial of a one-column shape

A Young diagram with at most one column has one cell in each of its rows, and a semistandard
tableau of that shape is exactly a strictly increasing list of letters, one per row: the entries
of a column increase strictly downwards, and there is no row condition to satisfy.  So a bounded
tableau of a one-column shape is nothing but the **set** of the letters it uses, and its weight is
the indicator of that set.  Summing over the tableaux therefore sums a squarefree monomial over
every set of letters of the right size, which is `MvPolynomial.esymm`:

`TauCeti.diagramSchurPoly N R μ = MvPolynomial.esymm (Fin N) R μ.card` for `μ.rowLen 0 ≤ 1`.

For partitions this reads `s_{(1ⁿ)} = e_n`, `TauCeti.schurPoly_ones`, the shape `(1ⁿ)` being the
`TauCeti.Nat.Partition.ones` at the bottom of the dominance order.  It is the `1 × 1` instance of
the dual Jacobi--Trudi identity, whose general form expresses `s_μ` as a determinant of elementary
symmetric polynomials, and the character-level shadow of `𝕊^{(1ⁿ)}(V) = ⋀ⁿ V`.

The identification runs through `TauCeti.BoundedSSYT.colFinsetEquiv`, the bijection between the
bounded tableaux of a one-column shape and the sets of letters of size the number of rows.  Both
directions are explicit: a tableau is sent to the set `TauCeti.BoundedSSYT.colFinset` of the
entries of its column, and a set is sent back to the tableau `TauCeti.BoundedSSYT.ofColFinset`
that lists it in increasing order, which is `Finset.orderEmbOfFin`.

Symmetry is a corollary rather than an input: the one-column case falls out of
`TauCeti.schurPoly_ones` and the symmetry of the elementary symmetric polynomials, without the
Bender--Knuth involution that `TauCeti.schurPoly_isSymmetric` needs in general.

## Main definitions

* `TauCeti.BoundedSSYT.colEntry`: the letter a bounded tableau puts in a given row of its first
  column.
* `TauCeti.BoundedSSYT.colFinset`: the set of letters used by the first column of a bounded
  tableau.
* `TauCeti.BoundedSSYT.ofColFinset`: the one-column tableau listing a given set of letters in
  increasing order.
* `TauCeti.BoundedSSYT.colFinsetEquiv`: the bijection between the bounded tableaux of a one-column
  shape and the sets of letters of size the number of rows.

## Main results

* `TauCeti.BoundedSSYT.weight_eq_sum_single`: the weight of a one-column tableau is the indicator
  of the set of letters it uses.
* `TauCeti.diagramSchurPoly_eq_esymm_of_rowLen_le_one`: the Schur polynomial of a one-column
  shape is an elementary symmetric polynomial.
* `TauCeti.schurPoly_ones`: `s_{(1ⁿ)} = e_n`.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3, where `s_{(1ⁿ)} = e_n` is the first example of a Schur function.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 7.
-/

namespace TauCeti

open Finset MvPolynomial

namespace BoundedSSYT

variable {N : ℕ} {μ : YoungDiagram}

/-! ### The first column of a bounded tableau -/

/-- The letter a bounded tableau puts in row `i` of its first column.  The shape enters only
through its number `μ.colLen 0` of rows, so this reads the first column of any bounded tableau;
for a one-column shape it reads the whole tableau. -/
def colEntry (T : BoundedSSYT N μ) (i : Fin (μ.colLen 0)) : Fin N :=
  ⟨T.1 i 0, entry_lt T (YoungDiagram.mem_iff_lt_colLen.mpr i.isLt)⟩

@[simp]
theorem colEntry_val (T : BoundedSSYT N μ) (i : Fin (μ.colLen 0)) :
    (colEntry T i : ℕ) = T.1 i 0 :=
  (rfl)

/-- **The first column of a bounded tableau increases strictly**, entries increasing strictly down
every column of a semistandard tableau. -/
theorem colEntry_strictMono (T : BoundedSSYT N μ) : StrictMono (colEntry T) := fun _ j hij =>
  T.1.col_strict hij (YoungDiagram.mem_iff_lt_colLen.mpr j.isLt)

/-- The set of letters the first column of a bounded tableau uses. -/
def colFinset (T : BoundedSSYT N μ) : Finset (Fin N) :=
  Finset.image (colEntry T) Finset.univ

/-- A letter is used by the first column of a bounded tableau exactly when some row carries it. -/
@[simp]
theorem mem_colFinset {T : BoundedSSYT N μ} {x : Fin N} :
    x ∈ colFinset T ↔ ∃ i, colEntry T i = x := by
  simp [colFinset]

/-- **The first column of a bounded tableau uses one letter per row**, its entries being
distinct. -/
@[simp]
theorem card_colFinset (T : BoundedSSYT N μ) : (colFinset T).card = μ.colLen 0 := by
  rw [colFinset, Finset.card_image_of_injective _ (colEntry_strictMono T).injective,
    Finset.card_univ, Fintype.card_fin]

/-- **The first column of a bounded tableau lists its letters in increasing order**: it is the
monotone enumeration `Finset.orderEmbOfFin` of the set of letters it uses. -/
theorem orderEmbOfFin_colFinset (T : BoundedSSYT N μ) :
    ⇑((colFinset T).orderEmbOfFin (card_colFinset T)) = colEntry T :=
  (Finset.orderEmbOfFin_unique _ (fun i => mem_colFinset.mpr ⟨i, rfl⟩)
    (colEntry_strictMono T)).symm

/-! ### The weight of a one-column tableau -/

/-- The cells of a one-column shape carrying a given letter, read off the rows that carry it. -/
private theorem filter_cells_eq_image (h : μ.rowLen 0 ≤ 1) (T : BoundedSSYT N μ) (y : Fin N) :
    (μ.cells.filter fun c => T.1 c.1 c.2 = (y : ℕ))
      = (Finset.univ.filter fun i : Fin (μ.colLen 0) => colEntry T i = y).image
          fun i : Fin (μ.colLen 0) => ((i : ℕ), 0) := by
  ext c
  obtain ⟨i, j⟩ := c
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    YoungDiagram.mem_cells, YoungDiagram.mem_iff_of_rowLen_le_one h, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hi, rfl⟩, hT⟩
    exact ⟨⟨i, hi⟩, Fin.ext hT, rfl, rfl⟩
  · rintro ⟨k, hk, rfl, rfl⟩
    exact ⟨⟨k.isLt, rfl⟩, congrArg Fin.val hk⟩

/-- A letter is used by at most one row, so it is used once if it occurs and not at all if it does
not. -/
private theorem card_filter_colEntry (T : BoundedSSYT N μ) (y : Fin N) :
    (Finset.univ.filter fun i : Fin (μ.colLen 0) => colEntry T i = y).card
      = if y ∈ colFinset T then 1 else 0 := by
  split_ifs with hy
  · obtain ⟨i, hi⟩ := mem_colFinset.mp hy
    have hsingle : (Finset.univ.filter fun j : Fin (μ.colLen 0) => colEntry T j = y) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hj => (colEntry_strictMono T).injective (hj.trans hi.symm), fun hj => hj ▸ hi⟩
    rw [hsingle, Finset.card_singleton]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun {i} _ hi => hy (mem_colFinset.mpr ⟨i, hi⟩)

/-- **The weight of a one-column tableau is the indicator of the set of letters it uses**: every
letter it uses is used exactly once, one column having at most one cell per row. -/
theorem weight_eq_sum_single (h : μ.rowLen 0 ≤ 1) (T : BoundedSSYT N μ) :
    weight T = ∑ x ∈ colFinset T, Finsupp.single x 1 := by
  ext y
  rw [weight_apply, SemistandardYoungTableau.content_apply, filter_cells_eq_image h T y,
    Finset.card_image_of_injective _ (fun i j hij => Fin.val_injective (congrArg Prod.fst hij)),
    card_filter_colEntry, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' (colFinset T) y fun _ => 1]

/-! ### Recovering a one-column tableau from its letters -/

/-- **The one-column tableau listing a given set of letters in increasing order.**  The letters
are read off by the monotone enumeration `Finset.orderEmbOfFin`, which needs the set to have one
letter per row of the shape; that is the hypothesis `hs`.  There is no row condition to check,
a one-column shape having at most one cell per row. -/
private def colTableau (h : μ.rowLen 0 ≤ 1) (s : Finset (Fin N)) (hs : s.card = μ.colLen 0) :
    _root_.SemistandardYoungTableau μ where
  entry i j := if hij : i < μ.colLen 0 ∧ j = 0 then (s.orderEmbOfFin hs ⟨i, hij.1⟩ : ℕ) else 0
  row_weak' := by
    intro i j1 j2 hj hcell
    obtain ⟨-, rfl⟩ := (YoungDiagram.mem_iff_of_rowLen_le_one h).mp hcell
    exact absurd hj (Nat.not_lt_zero j1)
  col_strict' := by
    intro i1 i2 j hi hcell
    obtain ⟨hi2, rfl⟩ := (YoungDiagram.mem_iff_of_rowLen_le_one h).mp hcell
    rw [dite_eq_left ⟨hi.trans hi2, rfl⟩, dite_eq_left ⟨hi2, rfl⟩]
    exact (s.orderEmbOfFin hs).strictMono hi
  zeros' := by
    intro i j hcell
    exact dite_eq_right fun hij => hcell ((YoungDiagram.mem_iff_of_rowLen_le_one h).mpr hij)

private theorem colTableau_apply (h : μ.rowLen 0 ≤ 1) (s : Finset (Fin N))
    (hs : s.card = μ.colLen 0) (i j : ℕ) :
    colTableau h s hs i j
      = if hij : i < μ.colLen 0 ∧ j = 0 then (s.orderEmbOfFin hs ⟨i, hij.1⟩ : ℕ) else 0 :=
  (rfl)

/-- **The one-column tableau listing a given set of letters in increasing order**, as a bounded
tableau: the letters it uses come from the alphabet because they are letters of the alphabet. -/
def ofColFinset (h : μ.rowLen 0 ≤ 1) (s : Finset (Fin N)) (hs : s.card = μ.colLen 0) :
    BoundedSSYT N μ :=
  ⟨colTableau h s hs, by
    intro i c hic
    obtain ⟨hi, rfl⟩ := (YoungDiagram.mem_iff_of_rowLen_le_one h).mp hic
    rw [colTableau_apply, dite_eq_left ⟨hi, rfl⟩]
    exact (s.orderEmbOfFin hs ⟨i, hi⟩).isLt⟩

theorem ofColFinset_apply (h : μ.rowLen 0 ≤ 1) (s : Finset (Fin N)) (hs : s.card = μ.colLen 0)
    (i j : ℕ) :
    (ofColFinset h s hs).1 i j
      = if hij : i < μ.colLen 0 ∧ j = 0 then (s.orderEmbOfFin hs ⟨i, hij.1⟩ : ℕ) else 0 :=
  colTableau_apply h s hs i j

@[simp]
theorem colEntry_ofColFinset (h : μ.rowLen 0 ≤ 1) (s : Finset (Fin N)) (hs : s.card = μ.colLen 0)
    (i : Fin (μ.colLen 0)) : colEntry (ofColFinset h s hs) i = s.orderEmbOfFin hs i :=
  Fin.ext <| by rw [colEntry_val, ofColFinset_apply, dite_eq_left ⟨i.isLt, rfl⟩]

@[simp]
theorem colFinset_ofColFinset (h : μ.rowLen 0 ≤ 1) (s : Finset (Fin N))
    (hs : s.card = μ.colLen 0) : colFinset (ofColFinset h s hs) = s := by
  rw [colFinset, funext (colEntry_ofColFinset h s hs)]
  exact s.image_orderEmbOfFin_univ hs

@[simp]
theorem ofColFinset_colFinset (h : μ.rowLen 0 ≤ 1) (T : BoundedSSYT N μ) :
    ofColFinset h (colFinset T) (card_colFinset T) = T := by
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
  rw [ofColFinset_apply]
  by_cases hij : (i, j) ∈ μ
  · obtain ⟨hi, rfl⟩ := (YoungDiagram.mem_iff_of_rowLen_le_one h).mp hij
    rw [dite_eq_left ⟨hi, rfl⟩, orderEmbOfFin_colFinset T, colEntry_val]
  · rw [dite_eq_right fun hc => hij ((YoungDiagram.mem_iff_of_rowLen_le_one h).mpr hc),
      T.1.zeros hij]

/-- **The bounded tableaux of a one-column shape are the sets of letters of the right size**: a
tableau is the set of the letters of its column, and a set of letters is listed down the column in
increasing order. -/
def colFinsetEquiv (h : μ.rowLen 0 ≤ 1) :
    BoundedSSYT N μ ≃ {s : Finset (Fin N) // s.card = μ.colLen 0} where
  toFun T := ⟨colFinset T, card_colFinset T⟩
  invFun s := ofColFinset h s.1 s.2
  left_inv T := ofColFinset_colFinset h T
  right_inv s := Subtype.ext (colFinset_ofColFinset h s.1 s.2)

@[simp]
theorem colFinsetEquiv_apply_coe (h : μ.rowLen 0 ≤ 1) (T : BoundedSSYT N μ) :
    (colFinsetEquiv h T : Finset (Fin N)) = colFinset T :=
  (rfl)

/-- The inverse of `colFinsetEquiv` lists a set of letters down the column in increasing order. -/
@[simp]
theorem colFinsetEquiv_symm_apply (h : μ.rowLen 0 ≤ 1)
    (s : {s : Finset (Fin N) // s.card = μ.colLen 0}) :
    (colFinsetEquiv h).symm s = ofColFinset h s.1 s.2 :=
  (rfl)

end BoundedSSYT

/-! ### The Schur polynomial of a one-column shape -/

variable {N : ℕ} {R : Type*} [CommSemiring R] {μ : YoungDiagram}

/-- **The Schur polynomial of a one-column shape is an elementary symmetric polynomial**: the
tableaux of that shape are the sets of letters of size the number of rows, each contributing the
squarefree monomial on the letters it uses. -/
theorem diagramSchurPoly_eq_esymm_of_rowLen_le_one (h : μ.rowLen 0 ≤ 1) :
    diagramSchurPoly N R μ = esymm (Fin N) R μ.card := by
  rw [YoungDiagram.card_eq_colLen_of_rowLen_le_one h, esymm_eq_sum_monomial,
    Finset.sum_subtype _ (fun _ => Finset.mem_powersetCard_univ) _, diagramSchurPoly_eq_sum]
  exact Fintype.sum_equiv (BoundedSSYT.colFinsetEquiv h) _ _ fun T =>
    congrArg (fun d => monomial d (1 : R)) (BoundedSSYT.weight_eq_sum_single h T)

section Partition

variable {σ : Type*} [Fintype σ]

/-- **The Schur polynomial of the one-column partition `(1ⁿ)` is the `n`-th elementary symmetric
polynomial**, `s_{(1ⁿ)} = e_n`. -/
@[simp]
theorem schurPoly_ones (n : ℕ) : schurPoly σ R (Nat.Partition.ones n) = esymm σ R n := by
  rw [schurPoly_eq_rename,
    diagramSchurPoly_eq_esymm_of_rowLen_le_one (rowLen_diagramOf_ones_le_one n 0),
    card_diagramOf, rename_esymm]

end Partition

end TauCeti
