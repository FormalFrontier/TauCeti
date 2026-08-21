/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot

/-!
# Computable Gauss-Jordan elimination

Mathlib says what it means for a matrix to be in (reduced) row echelon form
(`Matrix.IsRowEchelon`, `Matrix.IsReducedRowEchelon`, `Matrix.IsPivotedBy`) but has no algorithm
producing one. This file supplies the algorithm, as a genuine `def` on
`[DivisionRing F] [DecidableEq F]` data, together with its two correctness statements: the output
is in reduced row echelon form, and it spans the same subspace as the input.

The rows are carried as a `List (Fin n → F)` rather than as a matrix, because elimination changes
the number of rows it keeps: `TauCeti.rowReduce L` returns a list of pairs
`(pivot column, reduced row)`, one for each pivot, so the pivot data is part of the output rather
than something to be recovered from it afterwards.

The algorithm is Gauss-Jordan rather than plain Gaussian elimination: at each column a pivot row is
scaled to have a `1` there and is then subtracted from *every* other row, the rows already retained
included. So there is no back-substitution pass, and the invariant is maintained in one sweep over
the columns.

## Main definitions

* `TauCeti.rowReduce`: the reduced row echelon form of a list of rows, as a list of
  `(pivot column, row)` pairs.
* `TauCeti.rowReduceMatrix` and `TauCeti.rowReducePivot`: that output read as a matrix together
  with its pivot map.

## Main results

* `TauCeti.isReducedRowEchelon_rowReduceMatrix`: **the output is in reduced row echelon form**, and
  `TauCeti.isPivotedBy_rowReduceMatrix` identifies its pivots as the recorded columns. Since
  `Matrix.IsPivotedBy.rank_eq` reads the rank off the pivots, this gives
  `TauCeti.rank_rowReduceMatrix`: the reduced matrix has full row rank.
* `TauCeti.span_rowReduce`: **elimination preserves the row space**; the reduced rows span exactly
  what the original rows span.
* `TauCeti.length_rowReduce_ofFn`: the two together say that **the sweep computes the rank**, the
  number of pivots it records in the rows of a matrix being `Matrix.rank` of that matrix.

## Implementation notes

The sweep, the state it threads, and the invariant it maintains are all private, and no definition
here exposes its body: the supported interface is `TauCeti.rowReduce` together with the results
above, `TauCeti.rowReduceMatrix_apply` and `TauCeti.rowReducePivot_apply` standing in for the two
wrappers' bodies. So nothing downstream is committed to how the sweep represents its intermediate
data.

That state is a pair: the pivot rows found so far, each tagged with its pivot column, and the rows
not yet used as a pivot. A row that is used as a pivot is not removed from the second component;
subtracting the scaled pivot from it turns it into the zero row, which is harmless and saves the
algorithm (and every proof about it) from having to delete a list element. When the sweep reaches
the last column every row of the second component vanishes identically, which is what
`TauCeti.span_rowReduce` uses to discard it.

Only the columns are indexed by `Fin n`; the rows are an arbitrary list. Restricting the columns is
deliberate: the sweep must visit them in increasing order, and `List.finRange n` is the enumeration
that comes with the proof `List.pairwise_lt_finRange` that it does. The auxiliary sweep takes the
column list as an argument and the results about it assume only that the list is strictly
increasing, so the choice is confined to `TauCeti.rowReduce` itself.

Only `TauCeti.rank_rowReduceMatrix` and `TauCeti.length_rowReduce_ofFn` need `F` commutative:
`Matrix.rank` is defined over a commutative ring. Everything else, the algorithm included, works
over a division ring.

## References

Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
asks, as its computable finite-field linear algebra, for a `kernelBasis` obtained by "verified
Gaussian elimination"; this file is that elimination. Reading a basis of the kernel off the reduced
form is the step that remains: the free columns are those the pivots miss, and the entries of the
reduced rows in a free column are the coordinates of the corresponding kernel vector.
-/

public section

namespace TauCeti

universe u

section DivisionRing

variable {F : Type u} [DivisionRing F] [DecidableEq F] {n : ℕ}

/-! ## The algorithm -/

/-- The state of a Gauss-Jordan sweep: the pivot rows found so far, each tagged with its pivot
column, together with the rows not yet used as a pivot. -/
private abbrev RowReduceState (F : Type u) (n : ℕ) : Type u :=
  List (Fin n × (Fin n → F)) × List (Fin n → F)

/-- One column of a Gauss-Jordan sweep. If some unused row is nonzero in column `j`, scale the
first such row to have a `1` there, record it as the pivot row of column `j`, and subtract the
appropriate multiple of it from every other row, retained or not. Otherwise do nothing. -/
private def rowReduceStep (j : Fin n) (s : RowReduceState F n) : RowReduceState F n :=
  match s.2.find? fun w => decide (w j ≠ 0) with
  | none => s
  | some v =>
    let p := (v j)⁻¹ • v
    (s.1.map (fun q => (q.1, q.2 - q.2 j • p)) ++ [(j, p)], s.2.map fun w => w - w j • p)

/-- The idle branch of `TauCeti.rowReduceStep`: if no unused row is nonzero in column `j`, that
column of the sweep leaves the state alone. -/
private theorem rowReduceStep_of_find?_eq_none {j : Fin n} {s : RowReduceState F n}
    (h : s.2.find? (fun w => decide (w j ≠ 0)) = none) : rowReduceStep j s = s := by
  unfold rowReduceStep
  rw [h]

/-- The pivoting branch of `TauCeti.rowReduceStep`: if `v` is the first unused row nonzero in
column `j`, that column of the sweep records `(v j)⁻¹ • v` as the pivot row of `j` and clears
column `j` from every other row. -/
private theorem rowReduceStep_of_find?_eq_some {j : Fin n} {s : RowReduceState F n}
    {v : Fin n → F} (h : s.2.find? (fun w => decide (w j ≠ 0)) = some v) :
    rowReduceStep j s =
      (s.1.map (fun q => (q.1, q.2 - q.2 j • (v j)⁻¹ • v)) ++ [(j, (v j)⁻¹ • v)],
        s.2.map fun w => w - w j • (v j)⁻¹ • v) := by
  unfold rowReduceStep
  rw [h]

/-- A Gauss-Jordan sweep over the columns `cs`, taken in the order they are listed. -/
private def rowReduceAux : List (Fin n) → RowReduceState F n → RowReduceState F n
  | [], s => s
  | j :: cs, s => rowReduceAux cs (rowReduceStep j s)

/-- **The reduced row echelon form** of a list of rows: the list of pairs
`(pivot column, reduced row)`, one for each pivot, in increasing order of pivot column. -/
def rowReduce (L : List (Fin n → F)) : List (Fin n × (Fin n → F)) :=
  (rowReduceAux (List.finRange n) (([], L) : RowReduceState F n)).1

/-! ## The invariant -/

-- The state is spelled out below rather than written `RowReduceState F n`: a private structure
-- whose signature names a private abbreviation is not resolvable by the environment linters.
/-- The invariant a Gauss-Jordan sweep maintains, `cs` being the columns still to be visited: the
recorded pivot columns are strictly increasing and already visited, each recorded row has a `1` in
its own pivot column and a `0` in every other pivot column and everywhere to the left of its own,
and every unused row vanishes in every visited column. -/
private structure IsRowReduceState (cs : List (Fin n))
    (s : List (Fin n × (Fin n → F)) × List (Fin n → F)) : Prop where
  /-- Every recorded pivot column precedes every column still to be visited. -/
  pivot_lt : ∀ q ∈ s.1, ∀ j ∈ cs, q.1 < j
  /-- The recorded pivot columns are strictly increasing. -/
  pivot_pairwise : (s.1.map Prod.fst).Pairwise (· < ·)
  /-- Each recorded row has a `1` in its own pivot column. -/
  self : ∀ q ∈ s.1, q.2 q.1 = 1
  /-- Each recorded row vanishes to the left of its own pivot column. -/
  eq_zero_of_lt : ∀ q ∈ s.1, ∀ d, d < q.1 → q.2 d = 0
  /-- Each recorded row vanishes in every other recorded pivot column. -/
  eq_zero_of_ne : ∀ q ∈ s.1, ∀ q' ∈ s.1, q'.1 ≠ q.1 → q.2 q'.1 = 0
  /-- Every unused row vanishes in every column already visited. -/
  todo_eq_zero : ∀ w ∈ s.2, ∀ d, d ∉ cs → w d = 0

omit [DecidableEq F] in
/-- A sweep starts in a valid state: nothing has been recorded and no column has been visited. -/
private theorem isRowReduceState_nil (L : List (Fin n → F)) :
    IsRowReduceState (List.finRange n) (([], L) : RowReduceState F n) where
  pivot_lt := by simp
  pivot_pairwise := by simp
  self := by simp
  eq_zero_of_lt := by simp
  eq_zero_of_ne := by simp
  todo_eq_zero w _ d hd := absurd (List.mem_finRange d) hd

/-- One column of the sweep preserves the invariant. -/
private theorem isRowReduceState_rowReduceStep {cs : List (Fin n)} {j : Fin n}
    {s : RowReduceState F n} (hs : IsRowReduceState (j :: cs) s)
    (hcs : (j :: cs).Pairwise (· < ·)) :
    IsRowReduceState cs (rowReduceStep j s) := by
  have hgt : ∀ c ∈ cs, j < c := (List.pairwise_cons.mp hcs).1
  have hnotmem : ∀ d : Fin n, d < j → d ∉ j :: cs := by
    intro d hd hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact absurd hd (lt_irrefl d)
    · exact absurd (hgt d hmem) (not_lt.mpr hd.le)
  rcases hfind : s.2.find? (fun w => decide (w j ≠ 0)) with _ | v
  · have hzero : ∀ w ∈ s.2, w j = 0 := by
      intro w hw
      simpa using List.find?_eq_none.mp hfind w hw
    rw [rowReduceStep_of_find?_eq_none hfind]
    exact
      { pivot_lt := fun q hq c hc => hs.pivot_lt q hq c (List.mem_cons_of_mem _ hc)
        pivot_pairwise := hs.pivot_pairwise
        self := hs.self
        eq_zero_of_lt := hs.eq_zero_of_lt
        eq_zero_of_ne := hs.eq_zero_of_ne
        todo_eq_zero := fun w hw d hd => by
          rcases eq_or_ne d j with rfl | hne
          · exact hzero w hw
          · exact hs.todo_eq_zero w hw d (by simp [hne, hd]) }
  · have hv : v ∈ s.2 := List.mem_of_find?_eq_some hfind
    have hvj : v j ≠ 0 := by simpa using List.find?_some hfind
    set p : Fin n → F := (v j)⁻¹ • v with hpdef
    have hpj : p j = 1 := by simp [hpdef, inv_mul_cancel₀ hvj]
    have hp0 : ∀ d, d ∉ j :: cs → p d = 0 := fun d hd => by
      simp [hpdef, hs.todo_eq_zero v hv d hd]
    have hplow : ∀ d : Fin n, d < j → p d = 0 := fun d hd => hp0 d (hnotmem d hd)
    have hppivot : ∀ q ∈ s.1, p q.1 = 0 := fun q hq =>
      hplow q.1 (hs.pivot_lt q hq j List.mem_cons_self)
    have hstep : rowReduceStep j s =
        (s.1.map (fun q => (q.1, q.2 - q.2 j • p)) ++ [(j, p)], s.2.map fun w => w - w j • p) := by
      rw [rowReduceStep_of_find?_eq_some hfind, hpdef]
    rw [hstep]
    constructor
    · rintro q hq c hc
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hq
      rcases hq with ⟨q', hq', rfl⟩ | rfl
      · exact hs.pivot_lt q' hq' c (List.mem_cons_of_mem _ hc)
      · exact hgt c hc
    · rw [List.map_append, List.map_map]
      refine List.pairwise_append.mpr ⟨?_, by simp, ?_⟩
      · exact hs.pivot_pairwise
      · simp only [List.mem_map, List.map_cons, List.map_nil, List.mem_singleton,
          Function.comp_apply]
        rintro a ⟨q', hq', rfl⟩ b hb
        exact hb ▸ hs.pivot_lt q' hq' j List.mem_cons_self
    · rintro q hq
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hq
      rcases hq with ⟨q', hq', rfl⟩ | rfl
      · simp [hs.self q' hq', hppivot q' hq']
      · exact hpj
    · rintro q hq d hd
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hq
      rcases hq with ⟨q', hq', rfl⟩ | rfl
      · have : d < j := hd.trans (hs.pivot_lt q' hq' j List.mem_cons_self)
        simp [hs.eq_zero_of_lt q' hq' d hd, hplow d this]
      · exact hplow d hd
    · rintro q hq q' hq' hne
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hq hq'
      rcases hq with ⟨a, ha, rfl⟩ | rfl <;> rcases hq' with ⟨b, hb, rfl⟩ | rfl
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hs.eq_zero_of_ne a ha b hb (by simpa using hne), hppivot b hb]
        simp
      · simp [hpj]
      · exact hppivot b hb
      · exact absurd rfl hne
    · rintro w hw d hd
      simp only [List.mem_map] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      rcases eq_or_ne d j with rfl | hne
      · simp [hpj]
      · have hdmem : d ∉ j :: cs := by simp [hne, hd]
        simp [hs.todo_eq_zero w' hw' d hdmem, hp0 d hdmem]

/-- A whole sweep preserves the invariant, and leaves no column unvisited. -/
private theorem isRowReduceState_rowReduceAux {cs : List (Fin n)} {s : RowReduceState F n}
    (hcs : cs.Pairwise (· < ·)) (hs : IsRowReduceState cs s) :
    IsRowReduceState [] (rowReduceAux cs s) := by
  induction cs generalizing s with
  | nil => exact hs
  | cons j cs ih =>
    rw [rowReduceAux]
    exact ih (List.pairwise_cons.mp hcs).2 (isRowReduceState_rowReduceStep hs hcs)

/-- The state a full sweep ends in is valid, with no column left to visit. -/
private theorem isRowReduceState_rowReduceAux_finRange (L : List (Fin n → F)) :
    IsRowReduceState [] (rowReduceAux (List.finRange n) (([], L) : RowReduceState F n)) :=
  isRowReduceState_rowReduceAux (List.pairwise_lt_finRange n) (isRowReduceState_nil L)

/-! ## The reduced rows -/

section Rows

variable (L : List (Fin n → F))

/-- The pivot columns of `TauCeti.rowReduce` are strictly increasing. -/
theorem pairwise_map_fst_rowReduce : ((rowReduce L).map Prod.fst).Pairwise (· < ·) :=
  (isRowReduceState_rowReduceAux_finRange L).pivot_pairwise

/-- Each reduced row has a `1` in its own pivot column. -/
theorem rowReduce_self {q : Fin n × (Fin n → F)} (hq : q ∈ rowReduce L) : q.2 q.1 = 1 :=
  (isRowReduceState_rowReduceAux_finRange L).self q hq

/-- Each reduced row vanishes to the left of its own pivot column. -/
theorem rowReduce_eq_zero_of_lt {q : Fin n × (Fin n → F)} (hq : q ∈ rowReduce L) {d : Fin n}
    (hd : d < q.1) : q.2 d = 0 :=
  (isRowReduceState_rowReduceAux_finRange L).eq_zero_of_lt q hq d hd

/-- Each reduced row vanishes in every other pivot column. -/
theorem rowReduce_eq_zero_of_ne {q q' : Fin n × (Fin n → F)} (hq : q ∈ rowReduce L)
    (hq' : q' ∈ rowReduce L) (hne : q'.1 ≠ q.1) : q.2 q'.1 = 0 :=
  (isRowReduceState_rowReduceAux_finRange L).eq_zero_of_ne q hq q' hq' hne

/-- Every row not used as a pivot has been eliminated: at the end of the sweep the unused rows all
vanish identically. -/
private theorem rowReduceAux_snd_eq_zero {w : Fin n → F}
    (hw : w ∈ (rowReduceAux (List.finRange n) (([], L) : RowReduceState F n)).2) : w = 0 := by
  funext d
  exact (isRowReduceState_rowReduceAux_finRange L).todo_eq_zero w hw d (by simp)

end Rows

/-! ## The output as a matrix in reduced row echelon form -/

/-- The reduced rows of `L`, read as a matrix. -/
def rowReduceMatrix (L : List (Fin n → F)) :
    Matrix (Fin (rowReduce L).length) (Fin n) F :=
  Matrix.of fun i => ((rowReduce L).get i).2

/-- The pivot map of `TauCeti.rowReduceMatrix`; no row is zero, so it never takes the value `⊤`. -/
def rowReducePivot (L : List (Fin n → F)) : Fin (rowReduce L).length → WithTop (Fin n) :=
  fun i => (((rowReduce L).get i).1 : WithTop (Fin n))

section Echelon

variable (L : List (Fin n → F))

/-- The `i`-th row of the reduced matrix is the `i`-th reduced row. -/
@[simp] theorem rowReduceMatrix_apply (i : Fin (rowReduce L).length) :
    rowReduceMatrix L i = ((rowReduce L).get i).2 := by
  unfold rowReduceMatrix
  rfl

/-- The pivot of the `i`-th row of the reduced matrix is its recorded column. -/
@[simp] theorem rowReducePivot_apply (i : Fin (rowReduce L).length) :
    rowReducePivot L i = (((rowReduce L).get i).1 : WithTop (Fin n)) := by
  unfold rowReducePivot
  rfl

/-- The pivot columns are strictly increasing along the rows. -/
theorem strictMono_fst_get_rowReduce :
    StrictMono fun i : Fin (rowReduce L).length => ((rowReduce L).get i).1 := by
  intro i i' hii'
  exact List.pairwise_iff_get.mp (List.pairwise_map.mp (pairwise_map_fst_rowReduce L)) i i' hii'

/-- The recorded column of a reduced row is its leading entry. -/
theorem isLeadingEntry_rowReduceMatrix (i : Fin (rowReduce L).length) :
    (rowReduceMatrix L).IsLeadingEntry i ((rowReduce L).get i).1 := by
  refine ⟨fun d hd => rowReduce_eq_zero_of_lt L (List.get_mem _ _) hd, ?_⟩
  rw [rowReduceMatrix_apply, rowReduce_self L (List.get_mem _ _)]
  exact one_ne_zero

/-- **The pivots of the reduced matrix are the recorded columns.** -/
theorem isPivotedBy_rowReduceMatrix :
    (rowReduceMatrix L).IsPivotedBy (rowReducePivot L) := by
  refine Matrix.isPivotedBy_iff'.mpr ⟨?_, ?_, fun i => Or.inr ⟨_, rfl, ?_⟩⟩
  · exact fun i i' hii' => WithTop.coe_le_coe.mpr ((strictMono_fst_get_rowReduce L).monotone hii')
  · exact fun i _ i' _ hii' => WithTop.coe_lt_coe.mpr (strictMono_fst_get_rowReduce L hii')
  · exact isLeadingEntry_rowReduceMatrix L i

/-- **The output of Gauss-Jordan elimination is in reduced row echelon form.** -/
theorem isReducedRowEchelon_rowReduceMatrix :
    (rowReduceMatrix L).IsReducedRowEchelon where
  isRowEchelon := (isPivotedBy_rowReduceMatrix L).isRowEchelon
  eq_one i c hc := by
    obtain rfl := (isLeadingEntry_rowReduceMatrix L i).unique hc
    rw [rowReduceMatrix_apply]
    exact rowReduce_self L (List.get_mem _ _)
  eq_zero i i' c hii' hc := by
    obtain rfl := (isLeadingEntry_rowReduceMatrix L i').unique hc
    rw [rowReduceMatrix_apply]
    exact rowReduce_eq_zero_of_ne L (List.get_mem _ _) (List.get_mem _ _)
      ((strictMono_fst_get_rowReduce L).injective.ne hii'.ne')

/-- The rows of `TauCeti.rowReduceMatrix` are exactly the reduced rows. -/
theorem range_row_rowReduceMatrix :
    Set.range (rowReduceMatrix L).row = {v | v ∈ (rowReduce L).map Prod.snd} := by
  ext v
  simp only [Set.mem_range, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(rowReduce L).get i, List.get_mem _ _, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hq
    exact ⟨i, rfl⟩

end Echelon

/-! ## Elimination preserves the row space -/

/-- The row space of an elimination state: the span of the rows it still carries, recorded and
unused alike. -/
private def rowSpan (s : RowReduceState F n) : Submodule F (Fin n → F) :=
  Submodule.span F {v | v ∈ s.1.map Prod.snd ++ s.2}

omit [DecidableEq F] in
/-- A recorded row lies in the row space of its state. -/
private theorem mem_rowSpan_of_mem_fst {s : RowReduceState F n} {q : Fin n × (Fin n → F)}
    (hq : q ∈ s.1) : q.2 ∈ rowSpan s := by
  refine Submodule.subset_span ?_
  simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_map]
  exact Or.inl ⟨q, hq, rfl⟩

omit [DecidableEq F] in
/-- An unused row lies in the row space of its state. -/
private theorem mem_rowSpan_of_mem_snd {s : RowReduceState F n} {w : Fin n → F} (hw : w ∈ s.2) :
    w ∈ rowSpan s := by
  refine Submodule.subset_span ?_
  simp only [Set.mem_ofPred_eq, List.mem_append]
  exact Or.inr hw

omit [DecidableEq F] in
/-- The row space is the smallest submodule containing every row the state carries. -/
private theorem rowSpan_le {s : RowReduceState F n} {p : Submodule F (Fin n → F)}
    (h₁ : ∀ q ∈ s.1, q.2 ∈ p) (h₂ : ∀ w ∈ s.2, w ∈ p) : rowSpan s ≤ p := by
  refine Submodule.span_le.mpr ?_
  rintro v hv
  simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_map] at hv
  rcases hv with ⟨q, hq, rfl⟩ | hv
  · exact h₁ q hq
  · exact h₂ v hv

/-- One column of the sweep preserves the row space. -/
private theorem rowSpan_rowReduceStep (j : Fin n) (s : RowReduceState F n) :
    rowSpan (rowReduceStep j s) = rowSpan s := by
  rcases hfind : s.2.find? (fun w => decide (w j ≠ 0)) with _ | v
  · rw [rowReduceStep_of_find?_eq_none hfind]
  · have hv : v ∈ s.2 := List.mem_of_find?_eq_some hfind
    set p : Fin n → F := (v j)⁻¹ • v with hpdef
    have hstep : rowReduceStep j s =
        (s.1.map (fun q => (q.1, q.2 - q.2 j • p)) ++ [(j, p)], s.2.map fun w => w - w j • p) := by
      rw [rowReduceStep_of_find?_eq_some hfind, hpdef]
    have hp : p ∈ rowSpan s := Submodule.smul_mem _ _ (mem_rowSpan_of_mem_snd hv)
    rw [hstep]
    have hp' : p ∈ rowSpan (s.1.map (fun q => (q.1, q.2 - q.2 j • p)) ++ [(j, p)],
        s.2.map fun w => w - w j • p) :=
      mem_rowSpan_of_mem_fst (q := (j, p)) (by simp)
    refine le_antisymm (rowSpan_le ?_ ?_) (rowSpan_le ?_ ?_)
    · rintro q hq
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hq
      rcases hq with ⟨q', hq', rfl⟩ | rfl
      · exact Submodule.sub_mem _ (mem_rowSpan_of_mem_fst hq') (Submodule.smul_mem _ _ hp)
      · exact hp
    · rintro w hw
      simp only [List.mem_map] at hw
      obtain ⟨w', hw', rfl⟩ := hw
      exact Submodule.sub_mem _ (mem_rowSpan_of_mem_snd hw') (Submodule.smul_mem _ _ hp)
    · intro q hq
      have hmem : ((q.1, q.2 - q.2 j • p) :
          Fin n × (Fin n → F)) ∈ s.1.map (fun q => (q.1, q.2 - q.2 j • p)) ++ [(j, p)] := by
        simp only [List.mem_append, List.mem_map]
        exact Or.inl ⟨q, hq, rfl⟩
      have hq' := mem_rowSpan_of_mem_fst
        (s := (s.1.map (fun q => (q.1, q.2 - q.2 j • p)) ++ [(j, p)], s.2.map fun w => w - w j • p))
        hmem
      simpa using Submodule.add_mem _ hq' (Submodule.smul_mem _ (q.2 j) hp')
    · intro w hw
      have hmem : w - w j • p ∈ s.2.map (fun w => w - w j • p) := by
        simp only [List.mem_map]
        exact ⟨w, hw, rfl⟩
      have hw' := mem_rowSpan_of_mem_snd
        (s := (s.1.map (fun q => (q.1, q.2 - q.2 j • p)) ++ [(j, p)], s.2.map fun w => w - w j • p))
        hmem
      simpa using Submodule.add_mem _ hw' (Submodule.smul_mem _ (w j) hp')

/-- A whole sweep preserves the row space. -/
private theorem rowSpan_rowReduceAux (cs : List (Fin n)) (s : RowReduceState F n) :
    rowSpan (rowReduceAux cs s) = rowSpan s := by
  induction cs generalizing s with
  | nil => rfl
  | cons j cs ih => rw [rowReduceAux, ih, rowSpan_rowReduceStep]

/-- **Gauss-Jordan elimination preserves the row space**: the reduced rows span exactly what the
original rows span. -/
theorem span_rowReduce (L : List (Fin n → F)) :
    Submodule.span F {v | v ∈ (rowReduce L).map Prod.snd} = Submodule.span F {v | v ∈ L} := by
  have hend : rowSpan (rowReduceAux (List.finRange n) (([], L) : RowReduceState F n)) =
      Submodule.span F {v | v ∈ L} := by
    rw [rowSpan_rowReduceAux]
    simp [rowSpan]
  rw [← hend]
  refine le_antisymm (Submodule.span_le.mpr fun v hv => Submodule.subset_span ?_)
    (rowSpan_le (fun q hq => Submodule.subset_span ?_) fun w hw => ?_)
  · simp only [Set.mem_ofPred_eq, List.mem_append]
    exact Or.inl hv
  · simp only [Set.mem_ofPred_eq, List.mem_map]
    exact ⟨q, hq, rfl⟩
  · rw [rowReduceAux_snd_eq_zero L hw]
    exact Submodule.zero_mem _

end DivisionRing

/-! ## The sweep computes the rank

`Matrix.rank` is defined over a commutative ring, so these two results, alone in this file, ask
`F` to be a field. -/

section Field

variable {F : Type u} [Field F] [DecidableEq F] {n : ℕ} (L : List (Fin n → F))

/-- The reduced matrix has full row rank: every one of its rows is a pivot row. -/
theorem rank_rowReduceMatrix : (rowReduceMatrix L).rank = (rowReduce L).length := by
  rw [(isPivotedBy_rowReduceMatrix L).rank_eq]
  simp

/-- **Gauss-Jordan elimination computes the rank**: the number of pivots the sweep records in the
rows of a matrix is the rank of that matrix. -/
theorem length_rowReduce_ofFn {m : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    (rowReduce (List.ofFn A)).length = A.rank := by
  have hrows : Set.range A.row = {v | v ∈ List.ofFn A} := by
    ext v
    exact (List.mem_ofFn' A v).symm
  rw [← rank_rowReduceMatrix, Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row,
    range_row_rowReduceMatrix, hrows, span_rowReduce]

end Field

end TauCeti
