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
# The Schur polynomial of a one-row shape

A Young diagram with at most one row has one cell in each of its columns, and a semistandard
tableau of that shape is exactly a weakly increasing list of letters, one per column: the entries
of a row increase weakly rightwards, and there is no column condition to satisfy.  So a bounded
tableau of a one-row shape is nothing but the **multiset** of the letters it uses, and its weight
is the multiplicity function of that multiset.  Summing over the tableaux therefore sums the
monomial `∏ᵢ xᵢ ^ (multiplicity of i)` over every multiset of letters of the right size, which is
`MvPolynomial.hsymm`:

`TauCeti.diagramSchurPoly N R μ = MvPolynomial.hsymm (Fin N) R μ.card` for `μ.colLen 0 ≤ 1`.

For partitions this reads `s_{(n)} = h_n`, `TauCeti.schurPoly_indiscrete`, the shape `(n)` being
Mathlib's `Nat.Partition.indiscrete` at the top of the dominance order: a single row of `n` cells
for `n > 0`, and the empty diagram for `n = 0`.  It is the `1 × 1` instance of the Jacobi--Trudi
identity, whose general form expresses `s_μ` as a determinant of complete homogeneous symmetric
polynomials, and the character-level shadow of `𝕊^{(n)}(V) = Symⁿ V`.  It is dual to
`TauCeti.schurPoly_ones`, the one-column identity `s_{(1ⁿ)} = e_n`.

The identification runs through `TauCeti.BoundedSSYT.rowMultisetEquiv`, the bijection between the
bounded tableaux of a one-row shape and the multisets of letters of size the number of columns.
Both directions are explicit: a tableau is sent to the multiset
`TauCeti.BoundedSSYT.rowMultiset` of the entries of its row, and a multiset is sent back to the
tableau `TauCeti.BoundedSSYT.ofRowMultiset` that lists it in increasing order, along the sorted
word `Multiset.sort` produces.

Unlike the one-column case, where the letters of a tableau are pairwise distinct and form a
`Finset`, a row may repeat a letter, so the enumeration `Finset.orderEmbOfFin` is unavailable and
the sorted word is what carries the construction.  Its two characterising properties, that it is
weakly increasing and that it has the right multiset of letters, determine it
(`List.Perm.eq_of_pairwise'`), which is how the round trip from a tableau back to itself is
proved.

Symmetry is a corollary rather than an input:
`TauCeti.schurPoly_indiscrete_isSymmetric` records the one-row case of the symmetry of the Schur
polynomials, which is proved here without the Bender--Knuth involution that the general case
needs.

## Main definitions

* `TauCeti.BoundedSSYT.rowEntry`: the letter a bounded tableau puts in a given column of its first
  row.
* `TauCeti.BoundedSSYT.rowMultiset`: the multiset of letters used by the first row of a bounded
  tableau.
* `TauCeti.BoundedSSYT.ofRowMultiset`: the one-row tableau listing a given multiset of letters in
  increasing order.
* `TauCeti.BoundedSSYT.rowMultisetEquiv`: the bijection between the bounded tableaux of a one-row
  shape and the multisets of letters of size the number of columns.

## Main results

* `TauCeti.BoundedSSYT.weight_eq_toFinsupp`: the weight of a one-row tableau is the multiplicity
  function of the multiset of letters it uses.
* `TauCeti.diagramSchurPoly_eq_hsymm_of_colLen_le_one`: the Schur polynomial of a one-row shape is
  a complete homogeneous symmetric polynomial.
* `TauCeti.schurPoly_indiscrete`: `s_{(n)} = h_n`.
* `TauCeti.schurPoly_indiscrete_isSymmetric`: the Schur polynomial of the partition `(n)` is
  symmetric.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3, where `s_{(n)} = h_n` sits beside `s_{(1ⁿ)} = e_n` as the first examples of a Schur
  function.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 7.
-/

namespace TauCeti

open Finset MvPolynomial

/-! ### Monomials as products of variables -/

/-- **A monomial is the product of the variables it uses, with multiplicity.**  This is the form
in which the monomials of `MvPolynomial.hsymm` are written. -/
private theorem prod_map_X_eq_monomial {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ R)).prod = monomial s.toFinsupp (1 : R) := by
  rw [Finset.prod_multiset_map_count, ← prod_X_pow_eq_monomial, Multiset.toFinsupp_support]
  exact Finset.prod_congr rfl fun a _ => by rw [Multiset.toFinsupp_apply]

namespace BoundedSSYT

variable {N : ℕ} {μ : YoungDiagram}

/-! ### The first row of a bounded tableau -/

/-- The letter a bounded tableau puts in column `j` of its first row.  The shape enters only
through the length `μ.rowLen 0` of its first row, so this reads the first row of any bounded
tableau; for a one-row shape it reads the whole tableau. -/
def rowEntry (T : BoundedSSYT N μ) (j : Fin (μ.rowLen 0)) : Fin N :=
  ⟨T.1 0 j, entry_lt T (YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt)⟩

@[simp]
theorem rowEntry_val (T : BoundedSSYT N μ) (j : Fin (μ.rowLen 0)) :
    (rowEntry T j : ℕ) = T.1 0 j :=
  (rfl)

/-- **The first row of a bounded tableau increases weakly**, entries increasing weakly rightwards
along every row of a semistandard tableau. -/
theorem rowEntry_monotone (T : BoundedSSYT N μ) : Monotone (rowEntry T) := by
  intro j₁ j₂ hj
  rw [Fin.le_def, rowEntry_val, rowEntry_val]
  rcases Nat.eq_or_lt_of_le (Fin.le_def.mp hj) with h | h
  · exact le_of_eq (congrArg (T.1 0) h)
  · exact T.1.row_weak h (YoungDiagram.mem_iff_lt_rowLen.mpr j₂.isLt)

/-- The multiset of letters the first row of a bounded tableau uses, with multiplicity. -/
def rowMultiset (T : BoundedSSYT N μ) : Multiset (Fin N) :=
  Finset.univ.val.map (rowEntry T)

/-- A letter is used by the first row of a bounded tableau exactly when some column carries it. -/
@[simp]
theorem mem_rowMultiset {T : BoundedSSYT N μ} {x : Fin N} :
    x ∈ rowMultiset T ↔ ∃ j, rowEntry T j = x := by
  simp [rowMultiset]

/-- **The first row of a bounded tableau uses one letter per column**, counted with
multiplicity. -/
@[simp]
theorem card_rowMultiset (T : BoundedSSYT N μ) :
    Multiset.card (rowMultiset T) = μ.rowLen 0 := by
  simp [rowMultiset]

/-! ### The weight of a one-row tableau -/

/-- The cells of a one-row shape carrying a given letter, read off the columns that carry it. -/
private theorem filter_cells_eq_image (h : μ.colLen 0 ≤ 1) (T : BoundedSSYT N μ) (y : Fin N) :
    (μ.cells.filter fun c => T.1 c.1 c.2 = (y : ℕ))
      = (Finset.univ.filter fun j : Fin (μ.rowLen 0) => rowEntry T j = y).image
          fun j : Fin (μ.rowLen 0) => (0, (j : ℕ)) := by
  ext c
  obtain ⟨i, j⟩ := c
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    YoungDiagram.mem_cells, YoungDiagram.mem_iff_of_colLen_le_one h, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨rfl, hj⟩, hT⟩
    exact ⟨⟨j, hj⟩, Fin.ext hT, rfl, rfl⟩
  · rintro ⟨k, hk, rfl, rfl⟩
    exact ⟨⟨rfl, k.isLt⟩, congrArg Fin.val hk⟩

/-- **The weight of a one-row tableau counts the letters of its row**: a letter is used as often
as it occurs in the row. -/
theorem weight_apply_eq_count (h : μ.colLen 0 ≤ 1) (T : BoundedSSYT N μ) (y : Fin N) :
    weight T y = Multiset.count y (rowMultiset T) := by
  rw [weight_apply, SemistandardYoungTableau.content_apply, filter_cells_eq_image h T y,
    Finset.card_image_of_injective _ fun a b hab => Fin.val_injective (congrArg Prod.snd hab),
    rowMultiset, Multiset.count_map]
  simp [Finset.card, Finset.filter_val, eq_comm]

/-- **The weight of a one-row tableau is the multiplicity function of the letters of its row.** -/
theorem weight_eq_toFinsupp (h : μ.colLen 0 ≤ 1) (T : BoundedSSYT N μ) :
    weight T = (rowMultiset T).toFinsupp := by
  ext y
  rw [weight_apply_eq_count h T y, Multiset.toFinsupp_apply]

/-! ### Recovering a one-row tableau from its letters -/

/-- A multiset of letters, listed in increasing order and read as natural numbers: the first row
of the tableau `TauCeti.BoundedSSYT.ofRowMultiset`.  Unlike the one-column case, a row may repeat
a letter, so this is a genuine sorted word rather than the monotone enumeration of a set.  It is
an implementation detail: the tableau it builds is characterised, representation-independently, by
the round trips `TauCeti.BoundedSSYT.rowMultiset_ofRowMultiset` and
`TauCeti.BoundedSSYT.ofRowMultiset_rowMultiset`. -/
private def rowList (s : Multiset (Fin N)) : List ℕ :=
  (s.map Fin.val).sort (· ≤ ·)

@[simp]
private theorem coe_rowList (s : Multiset (Fin N)) :
    ((rowList s : List ℕ) : Multiset ℕ) = s.map Fin.val :=
  Multiset.sort_eq _ _

@[simp]
private theorem length_rowList (s : Multiset (Fin N)) :
    (rowList s).length = Multiset.card s := by
  rw [rowList, Multiset.length_sort, Multiset.card_map]

private theorem pairwise_rowList (s : Multiset (Fin N)) : (rowList s).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

private theorem rowList_lt {s : Multiset (Fin N)} {x : ℕ} (hx : x ∈ rowList s) : x < N := by
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp ((Multiset.mem_sort _).mp hx)
  exact y.isLt

/-- **The one-row tableau listing a given multiset of letters in increasing order.**  The multiset
must have one letter per column of the shape; that is the hypothesis `hs`.  There is no column
condition to check, a one-row shape having at most one cell per column. -/
private def rowTableau (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) : _root_.SemistandardYoungTableau μ where
  entry i j := if i = 0 then (rowList s).getD j 0 else 0
  row_weak' := by
    intro i j₁ j₂ hj hcell
    obtain ⟨rfl, hj₂⟩ := (YoungDiagram.mem_iff_of_colLen_le_one h).mp hcell
    have hlen : (rowList s).length = μ.rowLen 0 := (length_rowList s).trans hs
    rw [ite_eq_left rfl, ite_eq_left rfl, List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega)]
    exact List.pairwise_iff_getElem.mp (pairwise_rowList s) _ _ _ _ hj
  col_strict' := by
    intro i₁ i₂ j hi hcell
    obtain ⟨rfl, -⟩ := (YoungDiagram.mem_iff_of_colLen_le_one h).mp hcell
    exact absurd hi (Nat.not_lt_zero i₁)
  zeros' := by
    intro i j hcell
    by_cases hi : i = 0
    · subst hi
      have hlen : (rowList s).length = μ.rowLen 0 := (length_rowList s).trans hs
      have hj : ¬ j < μ.rowLen 0 := fun hj =>
        hcell ((YoungDiagram.mem_iff_of_colLen_le_one h).mpr ⟨rfl, hj⟩)
      rw [ite_eq_left rfl]
      exact List.getD_eq_default _ _ (by omega)
    · exact ite_eq_right hi

private theorem rowTableau_apply (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) (i j : ℕ) :
    rowTableau h s hs i j = if i = 0 then (rowList s).getD j 0 else 0 :=
  (rfl)

/-- **The one-row tableau listing a given multiset of letters in increasing order**, as a bounded
tableau: the letters it uses come from the alphabet because they are letters of the alphabet. -/
def ofRowMultiset (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) : BoundedSSYT N μ :=
  ⟨rowTableau h s hs, by
    intro i c hic
    obtain ⟨rfl, hc⟩ := (YoungDiagram.mem_iff_of_colLen_le_one h).mp hic
    have hlen : (rowList s).length = μ.rowLen 0 := (length_rowList s).trans hs
    rw [rowTableau_apply, ite_eq_left rfl, List.getD_eq_getElem _ _ (by omega)]
    exact rowList_lt (List.getElem_mem _)⟩

private theorem ofRowMultiset_apply (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) (i j : ℕ) :
    (ofRowMultiset h s hs).1 i j = if i = 0 then (rowList s).getD j 0 else 0 :=
  rowTableau_apply h s hs i j

/-- The first row of `TauCeti.BoundedSSYT.ofRowMultiset` reads off the sorted word. -/
private theorem rowEntry_ofRowMultiset (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) (j : Fin (μ.rowLen 0)) :
    (rowEntry (ofRowMultiset h s hs) j : ℕ) = (rowList s).getD (j : ℕ) 0 := by
  rw [rowEntry_val, ofRowMultiset_apply, ite_eq_left rfl]

/-- Reading a sorted word off column by column recovers it. -/
private theorem ofFn_getD_rowList (s : Multiset (Fin N)) (hs : Multiset.card s = μ.rowLen 0) :
    (List.ofFn fun j : Fin (μ.rowLen 0) => (rowList s).getD (j : ℕ) 0) = rowList s := by
  have hlen : (rowList s).length = μ.rowLen 0 := (length_rowList s).trans hs
  refine List.ext_getElem (by simp [hlen]) fun k hk hk' => ?_
  rw [List.getElem_ofFn, List.getD_eq_getElem _ _ hk']

/-- **Listing a multiset of letters along a row uses exactly those letters**: the multiset of
letters of `TauCeti.BoundedSSYT.ofRowMultiset h s hs` is `s` again. -/
@[simp]
theorem rowMultiset_ofRowMultiset (h : μ.colLen 0 ≤ 1) (s : Multiset (Fin N))
    (hs : Multiset.card s = μ.rowLen 0) : rowMultiset (ofRowMultiset h s hs) = s := by
  -- `rowEntry_ofRowMultiset` reads the entries one at a time, so it has to be bundled into a
  -- function equality before it can rewrite under `Multiset.map`.
  have hentries : Fin.val ∘ rowEntry (ofRowMultiset h s hs)
      = fun j : Fin (μ.rowLen 0) => (rowList s).getD (j : ℕ) 0 :=
    funext fun j => rowEntry_ofRowMultiset h s hs j
  refine Multiset.map_injective (Fin.val_injective (n := N)) ?_
  rw [rowMultiset, Multiset.map_map, hentries, Fin.univ_val_map, ofFn_getD_rowList s hs,
    coe_rowList]

/-- **The row of a one-row tableau is already sorted**, so it is the sorted word of its own
multiset of letters. -/
private theorem rowList_rowMultiset (T : BoundedSSYT N μ) :
    rowList (rowMultiset T) = List.ofFn fun j : Fin (μ.rowLen 0) => (T.1 0 j : ℕ) := by
  refine List.Perm.eq_of_pairwise' (pairwise_rowList _) ?_ ?_
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact T.1.row_weak (Fin.lt_def.mp hij) (YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt)
  · rw [← Multiset.coe_eq_coe, coe_rowList, rowMultiset, Multiset.map_map, Fin.univ_val_map]
    rfl

/-- **A one-row tableau is determined by the letters it uses**: relisting the multiset of letters
of the row of `T` in increasing order recovers `T`. -/
@[simp]
theorem ofRowMultiset_rowMultiset (h : μ.colLen 0 ≤ 1) (T : BoundedSSYT N μ) :
    ofRowMultiset h (rowMultiset T) (card_rowMultiset T) = T := by
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
  rw [ofRowMultiset_apply, rowList_rowMultiset]
  by_cases hij : (i, j) ∈ μ
  · obtain ⟨rfl, hj⟩ := (YoungDiagram.mem_iff_of_colLen_le_one h).mp hij
    rw [ite_eq_left rfl, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
  · rw [T.1.zeros hij]
    by_cases hi : i = 0
    · subst hi
      rw [ite_eq_left rfl, List.getD_eq_default]
      simp only [List.length_ofFn]
      exact Nat.le_of_not_lt fun hj =>
        hij ((YoungDiagram.mem_iff_of_colLen_le_one h).mpr ⟨rfl, hj⟩)
    · rw [ite_eq_right hi]

/-- **The bounded tableaux of a one-row shape are the multisets of letters of the right size**: a
tableau is the multiset of the letters of its row, and a multiset of letters is listed along the
row in increasing order. -/
def rowMultisetEquiv (h : μ.colLen 0 ≤ 1) : BoundedSSYT N μ ≃ Sym (Fin N) μ.card where
  toFun T := ⟨rowMultiset T,
    (card_rowMultiset T).trans (YoungDiagram.card_eq_rowLen_of_colLen_le_one h).symm⟩
  invFun s := ofRowMultiset h s.1 (s.2.trans (YoungDiagram.card_eq_rowLen_of_colLen_le_one h))
  left_inv T := ofRowMultiset_rowMultiset h T
  right_inv s := Sym.ext (rowMultiset_ofRowMultiset h s.1 _)

@[simp]
theorem rowMultisetEquiv_apply_coe (h : μ.colLen 0 ≤ 1) (T : BoundedSSYT N μ) :
    (rowMultisetEquiv h T : Multiset (Fin N)) = rowMultiset T :=
  (rfl)

/-- The inverse of `rowMultisetEquiv` lists a multiset of letters along the row in increasing
order. -/
@[simp]
theorem rowMultisetEquiv_symm_apply (h : μ.colLen 0 ≤ 1) (s : Sym (Fin N) μ.card) :
    (rowMultisetEquiv h).symm s
      = ofRowMultiset h s.1 (s.2.trans (YoungDiagram.card_eq_rowLen_of_colLen_le_one h)) :=
  (rfl)

end BoundedSSYT

/-! ### The Schur polynomial of a one-row shape -/

variable {N : ℕ} {R : Type*} [CommSemiring R] {μ : YoungDiagram}

/-- **The Schur polynomial of a one-row shape is a complete homogeneous symmetric polynomial**:
the tableaux of that shape are the multisets of letters of size the number of columns, each
contributing the monomial on the letters it uses. -/
theorem diagramSchurPoly_eq_hsymm_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    diagramSchurPoly N R μ = hsymm (Fin N) R μ.card := by
  rw [diagramSchurPoly_eq_sum, hsymm]
  refine Fintype.sum_equiv (BoundedSSYT.rowMultisetEquiv h) _ _ fun T => ?_
  rw [prod_map_X_eq_monomial]
  exact congrArg (fun d => monomial d (1 : R)) (BoundedSSYT.weight_eq_toFinsupp h T)

section Partition

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **The Schur polynomial of the partition `(n)` is the `n`-th complete homogeneous symmetric
polynomial**, `s_{(n)} = h_n`.  The diagram of `(n)` has at most one row: it is a single row of
`n` cells for `n > 0`, and empty for `n = 0`. -/
@[simp]
theorem schurPoly_indiscrete (n : ℕ) :
    schurPoly σ R (Nat.Partition.indiscrete n) = hsymm σ R n := by
  rw [schurPoly_eq_rename,
    diagramSchurPoly_eq_hsymm_of_colLen_le_one (colLen_diagramOf_indiscrete_le_one n),
    card_diagramOf, rename_hsymm]

omit [DecidableEq σ] in
/-- **The Schur polynomial of the partition `(n)` is symmetric.**  This is the at-most-one-row
case of the symmetry of the Schur polynomials, which in general needs the Bender--Knuth involution
and is not proved here; for `(n)` it is the symmetry of the complete homogeneous symmetric
polynomials. -/
theorem schurPoly_indiscrete_isSymmetric (n : ℕ) :
    (schurPoly σ R (Nat.Partition.indiscrete n)).IsSymmetric := by
  classical
  rw [schurPoly_indiscrete]
  exact hsymm_isSymmetric σ R n

end Partition

end TauCeti
