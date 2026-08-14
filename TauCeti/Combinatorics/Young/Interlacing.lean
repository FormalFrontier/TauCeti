/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Combinatorics.Young.Kostka

/-!
# Interlacing shapes and the branching of bounded tableaux

A Young diagram `ν` **interlaces** `μ` when their row lengths alternate,
`μ₀ ≥ ν₀ ≥ μ₁ ≥ ν₁ ≥ ⋯`; equivalently `ν ⊆ μ` and the skew shape `μ / ν` is a *horizontal
strip*, having at most one cell in each column.  This file defines that relation,
`YoungDiagram.InterlacedBy`, packages the shapes interlacing a fixed `μ` and having at most
`n` rows as a `Finset`, `YoungDiagram.interlacingShapes`, and proves the combinatorial
heart of the `GLₙ₊₁ ↓ GLₙ` branching rule.

That heart is a bijection.  A semistandard tableau of shape `μ` written in the `n + 1` letters
`{0, …, n}` is the same thing as a choice of a shape `ν` interlacing `μ` together with a
semistandard tableau of shape `ν` written in the `n` letters `{0, …, n - 1}`: the cells carrying
the top letter `n` are exactly the cells of `μ / ν`.  Interlacing is precisely the condition making
this work.  One direction is easy — rows increase weakly, so in each row the cells with a small
entry form a prefix, and columns increase strictly, so `μᵢ₊₁ ≤ νᵢ`.  The converse is where
interlacing does its work: filling every cell of `μ / ν` with the single letter `n` keeps the
columns strict exactly because `μ / ν` has no two cells in a column, which is `μᵢ₊₁ ≤ νᵢ`.

The bijection is stated fibrewise, as `TauCeti.BoundedSSYT.fiberEquiv`: the tableaux of shape `μ`
whose sub-shape of small entries is a *given* `ν` are the tableaux of shape `ν`.  Phrasing it this
way keeps every type non-dependent, so the resulting sum decomposition
`TauCeti.BoundedSSYT.sum_eq_sum_interlacingShapes` needs no transport along an equality of shapes.

## Main definitions

* `YoungDiagram.InterlacedBy`: `InterlacedBy μ ν` says that `ν` interlaces `μ`, that is
  `μ.rowLen (i + 1) ≤ ν.rowLen i` and `ν.rowLen i ≤ μ.rowLen i` for every `i`.  The shape being
  interlaced is written first, as in `TauCeti.Interlaces` for integer sequences.
* `YoungDiagram.interlacingShapes`: the shapes interlacing `μ` with at most `n` rows.
* `TauCeti.BoundedSSYT.restrictShape`: the cells of `μ` whose entry is smaller than `n`.
* `TauCeti.BoundedSSYT.restrict` and `TauCeti.BoundedSSYT.extend`: erasing the cells carrying the
  top letter, and putting them back.

## Main results

* `TauCeti.BoundedSSYT.restrictShape_mem_interlacingShapes`: the sub-shape of small entries
  interlaces `μ` and has at most `n` rows.
* `TauCeti.BoundedSSYT.content_restrict`: erasing the top letter leaves unchanged how often each
  of the remaining letters occurs.
* `TauCeti.BoundedSSYT.fiberEquiv`: the tableaux of shape `μ` in `n + 1` letters with a given
  sub-shape `ν` of small entries are the tableaux of shape `ν` in `n` letters.
* `TauCeti.BoundedSSYT.sum_eq_sum_interlacingShapes`: the resulting decomposition of a sum over
  the tableaux of shape `μ`, indexed by the interlacing shapes, and
  `TauCeti.BoundedSSYT.card_eq_sum_interlacingShapes`: its counting form, the branching rule for
  the number of tableaux.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/RepresentationTheory/ClassicalGroups/README.md),
  Layer 6, "branching rules".
-/

public section

namespace YoungDiagram

variable {μ ν : _root_.YoungDiagram}

/-- `YoungDiagram.InterlacedBy μ ν` says that the Young diagram `ν` **interlaces** `μ`: the
two sequences of row lengths alternate, `μ₀ ≥ ν₀ ≥ μ₁ ≥ ν₁ ≥ ⋯`.  Equivalently `ν ⊆ μ` and the
skew shape `μ / ν` is a horizontal strip: no column of `μ` contains two of its cells.

As for the integer sequences of `TauCeti.Interlaces`, the shape being interlaced is written
first. -/
def InterlacedBy (μ ν : _root_.YoungDiagram) : Prop :=
  ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i ∧ ν.rowLen i ≤ μ.rowLen i

/-- Interlacing unfolded: the pair of inequalities at each row.  This is the introduction and
elimination rule for `YoungDiagram.InterlacedBy`, whose body is not exposed. -/
@[simp]
theorem interlacedBy_iff :
    InterlacedBy μ ν ↔ ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i ∧ ν.rowLen i ≤ μ.rowLen i :=
  Iff.rfl

/-- An interlacing shape reaches at least as far as the next row of the shape it interlaces. -/
theorem InterlacedBy.rowLen_succ_le (h : InterlacedBy μ ν) (i : ℕ) :
    μ.rowLen (i + 1) ≤ ν.rowLen i :=
  (h i).1

/-- An interlacing shape reaches no further than the shape it interlaces. -/
theorem InterlacedBy.rowLen_le (h : InterlacedBy μ ν) (i : ℕ) : ν.rowLen i ≤ μ.rowLen i :=
  (h i).2

/-- An interlacing shape is a sub-diagram. -/
theorem InterlacedBy.le (h : InterlacedBy μ ν) : ν ≤ μ :=
  le_of_forall_rowLen_le h.rowLen_le

/-- **A horizontal strip has at most one cell in a column**: if `ν` interlaces `μ`, then a cell of
`μ` strictly below row `i` already lies in `ν` at row `i`.  This is the form of interlacing that
keeps a column strict when the whole of `μ / ν` is filled with one letter. -/
theorem InterlacedBy.mem_of_lt (h : InterlacedBy μ ν) {i₁ i₂ j : ℕ} (hi : i₁ < i₂)
    (hc : ((i₂, j) : ℕ × ℕ) ∈ μ) : ((i₁, j) : ℕ × ℕ) ∈ ν :=
  _root_.YoungDiagram.mem_iff_lt_rowLen.mpr
    ((_root_.YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le
      ((μ.rowLen_anti (i₁ + 1) i₂ hi).trans (h.rowLen_succ_le i₁)))

/-- **The shapes interlacing `μ` with at most `n` rows.**  These index the summands of the
`GLₙ₊₁ ↓ GLₙ` branching rule; the row bound is genuine, since a shape may interlace `μ` and still
be too tall to be written in `n` letters. -/
noncomputable def interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram) :
    Finset _root_.YoungDiagram :=
  Set.Finite.toFinset (s := {ν : _root_.YoungDiagram | InterlacedBy μ ν ∧ ν.colLen 0 ≤ n})
    ((finite_Iic μ).subset fun _ h => Set.mem_Iic.mpr h.1.le)

@[simp]
theorem mem_interlacingShapes {n : ℕ} :
    ν ∈ interlacingShapes n μ ↔ InterlacedBy μ ν ∧ ν.colLen 0 ≤ n :=
  Set.Finite.mem_toFinset _

end YoungDiagram

namespace TauCeti

namespace BoundedSSYT

variable {n : ℕ} {μ ν : _root_.YoungDiagram}

/-- **The sub-shape of small entries**: the cells of `μ` whose entry is smaller than the top letter
`n`.  It is a Young diagram because the entries increase weakly to the right and downwards. -/
def restrictShape (T : BoundedSSYT (n + 1) μ) : _root_.YoungDiagram where
  cells := μ.cells.filter fun c => T.1 c.1 c.2 < n
  isLowerSet := by
    rintro c d hdc hc
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hc ⊢
    exact ⟨μ.isLowerSet hdc hc.1,
      lt_of_le_of_lt (SemistandardYoungTableau.entry_le_of_le T.1 hdc.1 hdc.2 hc.1) hc.2⟩

@[simp]
theorem mem_restrictShape {T : BoundedSSYT (n + 1) μ} {i j : ℕ} :
    ((i, j) : ℕ × ℕ) ∈ restrictShape T ↔ ((i, j) : ℕ × ℕ) ∈ μ ∧ T.1 i j < n :=
  Finset.mem_filter

/-- Reading the defining property of `TauCeti.BoundedSSYT.restrictShape` off an equation naming
it. -/
theorem mem_iff_of_restrictShape_eq {T : BoundedSSYT (n + 1) μ} (hν : restrictShape T = ν)
    {i j : ℕ} : ((i, j) : ℕ × ℕ) ∈ ν ↔ ((i, j) : ℕ × ℕ) ∈ μ ∧ T.1 i j < n := by
  subst hν; exact mem_restrictShape

/-- The sub-shape of small entries is a sub-diagram. -/
theorem restrictShape_le (T : BoundedSSYT (n + 1) μ) : restrictShape T ≤ μ := by
  rintro ⟨i, j⟩ hc
  exact (mem_restrictShape.mp hc).1

/-- **The sub-shape of small entries interlace the shape.**  Every cell of `μ` in row `i + 1`
carries an entry at most `n`, so column strictness makes the entry of the cell directly above it
smaller than `n`, and that cell is therefore small: this is the inequality `μᵢ₊₁ ≤ νᵢ`. -/
theorem interlacedBy_restrictShape (T : BoundedSSYT (n + 1) μ) :
    YoungDiagram.InterlacedBy μ (restrictShape T) :=
  fun i => ⟨YoungDiagram.le_rowLen_of_forall_mem fun j hj => by
      have hc : ((i + 1, j) : ℕ × ℕ) ∈ μ := _root_.YoungDiagram.mem_iff_lt_rowLen.mpr hj
      have hlt : T.1 i j < T.1 (i + 1) j := T.1.col_strict (Nat.lt_succ_self i) hc
      have hbound : T.1 (i + 1) j < n + 1 := entry_lt T hc
      exact mem_restrictShape.mpr ⟨μ.up_left_mem (Nat.le_succ i) le_rfl hc, by omega⟩,
    YoungDiagram.rowLen_le_of_le (restrictShape_le T) i⟩

/-- **The sub-shape of small entries is written in `n` letters**, so it has at most `n` rows: the
entry in row `i` is at least `i`. -/
theorem colLen_zero_restrictShape_le (T : BoundedSSYT (n + 1) μ) :
    (restrictShape T).colLen 0 ≤ n := by
  by_contra h
  have hmem : ((n, 0) : ℕ × ℕ) ∈ restrictShape T :=
    _root_.YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
  obtain ⟨hμ, hlt⟩ := mem_restrictShape.mp hmem
  exact absurd (SemistandardYoungTableau.le_entry T.1 hμ) (by omega)

/-- The sub-shape of small entries is one of the shapes the branching rule sums over. -/
theorem restrictShape_mem_interlacingShapes (T : BoundedSSYT (n + 1) μ) :
    restrictShape T ∈ YoungDiagram.interlacingShapes n μ :=
  YoungDiagram.mem_interlacingShapes.mpr
    ⟨interlacedBy_restrictShape T, colLen_zero_restrictShape_le T⟩

/-- **Erasing the top letter, as a filling**: keep the entries on the sub-shape `ν` of small
entries and drop the rest.  The shape is passed as a parameter, together with the equation
identifying it, so that the result lives in a type that does not depend on `T`.  Only the bounded
form `TauCeti.BoundedSSYT.restrict` is part of the interface. -/
private def restrictTableau (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram)
    (hν : restrictShape T = ν) : _root_.SemistandardYoungTableau ν where
  entry := fun i j => if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0
  row_weak' := fun {i j₁ j₂} hj hc => by
    have hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν := ν.up_left_mem le_rfl hj.le hc
    rw [ite_eq_left hc₁, ite_eq_left hc]
    exact T.1.row_weak hj ((mem_iff_of_restrictShape_eq hν).mp hc).1
  col_strict' := fun {i₁ i₂ j} hi hc => by
    have hc₁ : ((i₁, j) : ℕ × ℕ) ∈ ν := ν.up_left_mem hi.le le_rfl hc
    rw [ite_eq_left hc₁, ite_eq_left hc]
    exact T.1.col_strict hi ((mem_iff_of_restrictShape_eq hν).mp hc).1
  zeros' := fun {_ _} hc => ite_eq_right hc

/-- The entries of the filling underlying `TauCeti.BoundedSSYT.restrict`. -/
private theorem restrictTableau_apply (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram)
    (hν : restrictShape T = ν) (i j : ℕ) :
    restrictTableau T ν hν i j = if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0 :=
  (rfl)

/-- **Erasing the top letter**: a tableau of shape `μ` in the letters `{0, …, n}` restricts to a
tableau of shape `ν` in the letters `{0, …, n - 1}`, where `ν` is its sub-shape of small entries.
The shape is passed as a parameter, together with the equation identifying it, so that the result
lives in a type that does not depend on `T`. -/
def restrict (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram) (hν : restrictShape T = ν) :
    BoundedSSYT n ν :=
  ⟨restrictTableau T ν hν, fun i j hc => by
    rw [restrictTableau_apply, ite_eq_left hc]
    exact ((mem_iff_of_restrictShape_eq hν).mp hc).2⟩

/-- The entries of a restricted tableau. -/
@[simp]
theorem restrict_apply (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram)
    (hν : restrictShape T = ν) (i j : ℕ) :
    (restrict T ν hν).1 i j = if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0 :=
  restrictTableau_apply T ν hν i j

/-- **Erasing the top letter changes no other multiplicity**: the cells of `μ` carrying a letter
smaller than the top letter `n` are exactly the cells of the sub-shape `ν`, and there the two
tableaux agree, so each such letter occupies as many cells of `ν` as it does of `μ`. -/
@[simp]
theorem content_restrict (T : BoundedSSYT (n + 1) μ) (hν : restrictShape T = ν) {i : ℕ}
    (hi : i < n) :
    SemistandardYoungTableau.content (restrict T ν hν).1 i
      = SemistandardYoungTableau.content T.1 i := by
  have hcells : (ν.cells.filter fun c => (restrict T ν hν).1 c.1 c.2 = i)
      = μ.cells.filter fun c => T.1 c.1 c.2 = i := by
    ext c
    obtain ⟨a, b⟩ := c
    simp only [Finset.mem_filter, _root_.YoungDiagram.mem_cells, restrict_apply]
    constructor
    · rintro ⟨hc, hT⟩
      rw [ite_eq_left hc] at hT
      exact ⟨((mem_iff_of_restrictShape_eq hν).mp hc).1, hT⟩
    · rintro ⟨hc, hT⟩
      have hmem : ((a, b) : ℕ × ℕ) ∈ ν :=
        (mem_iff_of_restrictShape_eq hν).mpr ⟨hc, by rw [hT]; exact hi⟩
      exact ⟨hmem, by rw [ite_eq_left hmem]; exact hT⟩
  rw [SemistandardYoungTableau.content_apply, SemistandardYoungTableau.content_apply, hcells]

/-- **Restoring the top letter, as a filling**: keep the entries of `T` on `ν` and write the letter
`n` on every cell of `μ / ν`.  Columns stay strict because `ν` interlaces `μ`, so no column of
`μ / ν` holds two cells.  Only the bounded form `TauCeti.BoundedSSYT.extend` is part of the
interface. -/
private def extendTableau (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) :
    _root_.SemistandardYoungTableau μ where
  entry := fun i j =>
    if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0
  row_weak' := fun {i j₁ j₂} hj hc => by
    by_cases hc₂ : ((i, j₂) : ℕ × ℕ) ∈ ν
    · have hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν := ν.up_left_mem le_rfl hj.le hc₂
      rw [ite_eq_left hc₁, ite_eq_left hc₂]
      exact T.1.row_weak hj hc₂
    · rw [ite_eq_right hc₂, ite_eq_left hc]
      by_cases hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν
      · rw [ite_eq_left hc₁]
        exact (entry_lt T hc₁).le
      · rw [ite_eq_right hc₁, ite_eq_left (μ.up_left_mem le_rfl hj.le hc)]
  col_strict' := fun {i₁ i₂ j} hi hc => by
    have hc₁ : ((i₁, j) : ℕ × ℕ) ∈ ν := h.mem_of_lt hi hc
    rw [ite_eq_left hc₁]
    by_cases hc₂ : ((i₂, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hc₂]
      exact T.1.col_strict hi hc₂
    · rw [ite_eq_right hc₂, ite_eq_left hc]
      exact entry_lt T hc₁
  zeros' := fun {_ _} hc => by
    rw [ite_eq_right fun hν => hc (h.le hν), ite_eq_right hc]

/-- The entries of the filling underlying `TauCeti.BoundedSSYT.extend`. -/
private theorem extendTableau_apply (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν)
    (i j : ℕ) :
    extendTableau h T i j =
      if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0 :=
  (rfl)

/-- **Restoring the top letter**: filling every cell of `μ / ν` with the letter `n` turns a tableau
of shape `ν` in `n` letters into a tableau of shape `μ` in `n + 1` letters. -/
def extend (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) : BoundedSSYT (n + 1) μ :=
  ⟨extendTableau h T, fun i j hc => by
    rw [extendTableau_apply]
    by_cases hc₁ : ((i, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hc₁]
      exact Nat.lt_succ_of_lt (entry_lt T hc₁)
    · rw [ite_eq_right hc₁, ite_eq_left hc]
      exact Nat.lt_succ_self n⟩

/-- The entries of an extended tableau. -/
@[simp]
theorem extend_apply (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) (i j : ℕ) :
    (extend h T).1 i j =
      if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0 :=
  extendTableau_apply h T i j

/-- Restoring the top letter on the cells of `μ / ν` gives back `ν` as the sub-shape of small
entries. -/
@[simp]
theorem restrictShape_extend (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) :
    restrictShape (extend h T) = ν := by
  refine _root_.YoungDiagram.ext (Finset.ext fun c => ?_)
  obtain ⟨i, j⟩ := c
  simp only [_root_.YoungDiagram.mem_cells, mem_restrictShape, extend_apply]
  constructor
  · rintro ⟨hμ, hlt⟩
    by_contra hν
    rw [ite_eq_right hν, ite_eq_left hμ] at hlt
    exact absurd hlt (lt_irrefl n)
  · intro hν
    exact ⟨h.le hν, by rw [ite_eq_left hν]; exact entry_lt T hν⟩

/-- **The branching bijection, fibrewise.**  The tableaux of shape `μ` in the letters `{0, …, n}`
whose sub-shape of small entries is a given `ν` are exactly the tableaux of shape `ν` in the
letters `{0, …, n - 1}`: erasing and restoring the top letter are mutually inverse. -/
def fiberEquiv (h : YoungDiagram.InterlacedBy μ ν) :
    {T : BoundedSSYT (n + 1) μ // restrictShape T = ν} ≃ BoundedSSYT n ν where
  toFun T := restrict T.1 ν T.2
  invFun T := ⟨extend h T, restrictShape_extend h T⟩
  left_inv := by
    rintro ⟨T, hT⟩
    refine Subtype.ext (Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_))
    rw [extend_apply, restrict_apply]
    by_cases hν : ((i, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hν, ite_eq_left hν]
    · rw [ite_eq_right hν]
      by_cases hμ : ((i, j) : ℕ × ℕ) ∈ μ
      · rw [ite_eq_left hμ]
        have hnot : ¬ T.1 i j < n := fun hlt => hν ((mem_iff_of_restrictShape_eq hT).mpr ⟨hμ, hlt⟩)
        have hlt := entry_lt T hμ
        have heq : T.1 i j = n := by omega
        exact heq.symm
      · rw [ite_eq_right hμ]
        exact (T.1.zeros hμ).symm
  right_inv := by
    intro T
    refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
    rw [restrict_apply, extend_apply]
    by_cases hν : ((i, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hν, ite_eq_left hν]
    · rw [ite_eq_right hν]
      exact (T.1.zeros hν).symm

/-- The branching bijection erases the top letter. -/
@[simp]
theorem fiberEquiv_apply (h : YoungDiagram.InterlacedBy μ ν)
    (T : {T : BoundedSSYT (n + 1) μ // restrictShape T = ν}) :
    fiberEquiv h T = restrict T.1 ν T.2 :=
  (rfl)

/-- The inverse of the branching bijection restores the top letter. -/
@[simp]
theorem fiberEquiv_symm_apply (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) :
    (fiberEquiv h).symm T = ⟨extend h T, restrictShape_extend h T⟩ :=
  (rfl)

/-- **The branching decomposition of a sum over tableaux**: summing over the tableaux of shape `μ`
in the letters `{0, …, n}` is summing, over the shapes `ν` interlacing `μ` with at most `n` rows,
over the tableaux of shape `ν` in the letters `{0, …, n - 1}`. -/
theorem sum_eq_sum_interlacingShapes {M : Type*} [AddCommMonoid M] (n : ℕ)
    (μ : _root_.YoungDiagram) (f : ∀ ν : _root_.YoungDiagram, BoundedSSYT n ν → M) :
    ∑ T : BoundedSSYT (n + 1) μ, f (restrictShape T) (restrict T (restrictShape T) rfl)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, ∑ T : BoundedSSYT n ν, f ν T := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun T _ => restrictShape_mem_interlacingShapes T)
    (fun T => f (restrictShape T) (restrict T (restrictShape T) rfl))]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [Finset.sum_subtype (p := fun T : BoundedSSYT (n + 1) μ => restrictShape T = ν) _
    (fun T => by simp)]
  refine Fintype.sum_equiv (fiberEquiv (YoungDiagram.mem_interlacingShapes.mp hν).1) _ _
    fun T => ?_
  obtain ⟨T, hT⟩ := T
  subst hT
  rfl

/-- **The branching rule for the number of tableaux**: the tableaux of shape `μ` in `n + 1` letters
are counted by the tableaux of the shapes interlacing `μ`, written in `n` letters.  The statement
is purely combinatorial; when `μ` has at most `n + 1` rows it is, over `ℂ`, the counting shadow of
the multiplicity-free `GLₙ₊₁ ↓ GLₙ` branching of the irreducible of highest weight `μ`, whose
dimension is the number of such tableaux. -/
theorem card_eq_sum_interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram) :
    Fintype.card (BoundedSSYT (n + 1) μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, Fintype.card (BoundedSSYT n ν) := by
  simpa using sum_eq_sum_interlacingShapes n μ fun _ _ => (1 : ℕ)

end BoundedSSYT

end TauCeti
