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
`TauCeti.YoungDiagram.Interlaces`, packages the shapes interlacing a fixed `μ` and having at most
`n` rows as a `Finset`, `TauCeti.YoungDiagram.interlacingShapes`, and proves the combinatorial
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

* `TauCeti.YoungDiagram.Interlaces`: `ν` interlaces `μ`, that is `μ.rowLen (i + 1) ≤ ν.rowLen i`
  and `ν.rowLen i ≤ μ.rowLen i` for every `i`.
* `TauCeti.YoungDiagram.interlacingShapes`: the shapes interlacing `μ` with at most `n` rows.
* `TauCeti.BoundedSSYT.restrictShape`: the cells of `μ` whose entry is smaller than `n`.
* `TauCeti.BoundedSSYT.restrict` and `TauCeti.BoundedSSYT.extend`: erasing the cells carrying the
  top letter, and putting them back.

## Main results

* `TauCeti.BoundedSSYT.restrictShape_mem_interlacingShapes`: the sub-shape of small entries
  interlaces `μ` and has at most `n` rows.
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

namespace TauCeti

namespace YoungDiagram

variable {μ ν : _root_.YoungDiagram}

/-- A row of a sub-diagram is no longer than the corresponding row. -/
theorem rowLen_le_of_le (h : ν ≤ μ) (i : ℕ) : ν.rowLen i ≤ μ.rowLen i := by
  rcases Nat.eq_zero_or_pos (ν.rowLen i) with h0 | h0
  · omega
  · have hmem : ((i, ν.rowLen i - 1) : ℕ × ℕ) ∈ ν :=
      _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have := _root_.YoungDiagram.mem_iff_lt_rowLen.mp (h hmem)
    omega

/-- A Young diagram is contained in another as soon as each of its rows is shorter. -/
theorem le_of_forall_rowLen_le (h : ∀ i, ν.rowLen i ≤ μ.rowLen i) : ν ≤ μ := by
  rintro ⟨i, j⟩ hc
  exact _root_.YoungDiagram.mem_iff_lt_rowLen.mpr
    ((_root_.YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le (h i))

/-- Containment of Young diagrams is containment of rows. -/
theorem le_iff_forall_rowLen_le : ν ≤ μ ↔ ∀ i, ν.rowLen i ≤ μ.rowLen i :=
  ⟨fun h => rowLen_le_of_le h, le_of_forall_rowLen_le⟩

/-- A row of a Young diagram is at least as long as any initial segment of cells it contains. -/
theorem le_rowLen_of_forall_mem {i k : ℕ} (h : ∀ j < k, ((i, j) : ℕ × ℕ) ∈ ν) :
    k ≤ ν.rowLen i := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  · have := _root_.YoungDiagram.mem_iff_lt_rowLen.mp (h (k - 1) (by omega))
    omega

/-- `ν` **interlaces** `μ` when the two sequences of row lengths alternate,
`μ₀ ≥ ν₀ ≥ μ₁ ≥ ν₁ ≥ ⋯`.  Equivalently `ν ⊆ μ` and the skew shape `μ / ν` is a horizontal strip:
no column of `μ` contains two of its cells. -/
def Interlaces (ν μ : _root_.YoungDiagram) : Prop :=
  ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i ∧ ν.rowLen i ≤ μ.rowLen i

/-- An interlacing shape reaches at least as far as the next row of the shape it interlaces. -/
theorem Interlaces.rowLen_succ_le (h : Interlaces ν μ) (i : ℕ) :
    μ.rowLen (i + 1) ≤ ν.rowLen i :=
  (h i).1

/-- An interlacing shape reaches no further than the shape it interlaces. -/
theorem Interlaces.rowLen_le (h : Interlaces ν μ) (i : ℕ) : ν.rowLen i ≤ μ.rowLen i :=
  (h i).2

/-- An interlacing shape is a sub-diagram. -/
theorem Interlaces.le (h : Interlaces ν μ) : ν ≤ μ :=
  le_of_forall_rowLen_le h.rowLen_le

/-- **A horizontal strip has at most one cell in a column**: if `ν` interlaces `μ`, then a cell of
`μ` strictly below row `i` already lies in `ν` at row `i`.  This is the form of interlacing that
keeps a column strict when the whole of `μ / ν` is filled with one letter. -/
theorem Interlaces.mem_of_lt (h : Interlaces ν μ) {i₁ i₂ j : ℕ} (hi : i₁ < i₂)
    (hc : ((i₂, j) : ℕ × ℕ) ∈ μ) : ((i₁, j) : ℕ × ℕ) ∈ ν :=
  _root_.YoungDiagram.mem_iff_lt_rowLen.mpr
    ((_root_.YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le
      ((μ.rowLen_anti (i₁ + 1) i₂ hi).trans (h.rowLen_succ_le i₁)))

/-- A Young diagram has finitely many sub-diagrams, each being determined by its set of cells. -/
theorem finite_setOf_le (μ : _root_.YoungDiagram) : {ν : _root_.YoungDiagram | ν ≤ μ}.Finite := by
  have hinj : Set.InjOn _root_.YoungDiagram.cells {ν : _root_.YoungDiagram | ν ≤ μ} :=
    fun _ _ _ _ h => _root_.YoungDiagram.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine Set.Finite.subset (μ.cells.powerset : Finset (Finset (ℕ × ℕ))).finite_toSet ?_
  rintro s ⟨ξ, hξ, rfl⟩
  exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr fun c hc => hξ hc)

/-- **The shapes interlacing `μ` with at most `n` rows.**  These index the summands of the
`GLₙ₊₁ ↓ GLₙ` branching rule; the row bound is genuine, since a shape may interlace `μ` and still
be too tall to be written in `n` letters. -/
noncomputable def interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram) :
    Finset _root_.YoungDiagram :=
  Set.Finite.toFinset (s := {ν : _root_.YoungDiagram | Interlaces ν μ ∧ ν.colLen 0 ≤ n})
    ((finite_setOf_le μ).subset fun _ h => h.1.le)

@[simp]
theorem mem_interlacingShapes {n : ℕ} :
    ν ∈ interlacingShapes n μ ↔ Interlaces ν μ ∧ ν.colLen 0 ≤ n :=
  Set.Finite.mem_toFinset _

end YoungDiagram

namespace SemistandardYoungTableau

variable {μ : _root_.YoungDiagram}

/-- The entries of a semistandard Young tableau increase weakly to the right and downwards. -/
theorem entry_le_of_le (T : _root_.SemistandardYoungTableau μ) {i₁ i₂ j₁ j₂ : ℕ} (hi : i₁ ≤ i₂)
    (hj : j₁ ≤ j₂) (hc : ((i₂, j₂) : ℕ × ℕ) ∈ μ) : T i₁ j₁ ≤ T i₂ j₂ :=
  (T.row_weak_of_le hj (μ.up_left_mem hi le_rfl hc)).trans (T.col_weak hi hc)

end SemistandardYoungTableau

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

/-- **The sub-shape of small entries interlaces the shape.**  Below a cell with an entry smaller
than `n` the entry is still at most `n`, so the cell above it in the previous row is already
small: that is the inequality `μᵢ₊₁ ≤ νᵢ`. -/
theorem restrictShape_interlaces (T : BoundedSSYT (n + 1) μ) :
    YoungDiagram.Interlaces (restrictShape T) μ :=
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
    ⟨restrictShape_interlaces T, colLen_zero_restrictShape_le T⟩

/-- **Erasing the top letter**: a tableau of shape `μ` in the letters `{0, …, n}` restricts to a
tableau of shape `ν` in the letters `{0, …, n - 1}`, where `ν` is its sub-shape of small entries.
The shape is passed as a parameter, together with the equation identifying it, so that the result
lives in a type that does not depend on `T`. -/
def restrict (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram) (hν : restrictShape T = ν) :
    BoundedSSYT n ν :=
  ⟨{ entry := fun i j => if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0
     row_weak' := fun {i j₁ j₂} hj hc => by
       have hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν := ν.up_left_mem le_rfl hj.le hc
       rw [if_pos hc₁, if_pos hc]
       exact T.1.row_weak hj ((mem_iff_of_restrictShape_eq hν).mp hc).1
     col_strict' := fun {i₁ i₂ j} hi hc => by
       have hc₁ : ((i₁, j) : ℕ × ℕ) ∈ ν := ν.up_left_mem hi.le le_rfl hc
       rw [if_pos hc₁, if_pos hc]
       exact T.1.col_strict hi ((mem_iff_of_restrictShape_eq hν).mp hc).1
     zeros' := fun {_ _} hc => if_neg hc },
    fun i j hc => by
      change (if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0) < n
      rw [if_pos hc]
      exact ((mem_iff_of_restrictShape_eq hν).mp hc).2⟩

/-- The entries of a restricted tableau. -/
@[simp]
theorem restrict_apply (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram)
    (hν : restrictShape T = ν) (i j : ℕ) :
    (restrict T ν hν).1 i j = if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0 :=
  (rfl)

/-- **Restoring the top letter**: filling every cell of `μ / ν` with the letter `n` turns a tableau
of shape `ν` in `n` letters into a tableau of shape `μ` in `n + 1` letters.  Columns stay strict
because `ν` interlaces `μ`, so no column of `μ / ν` holds two cells. -/
def extend (h : YoungDiagram.Interlaces ν μ) (T : BoundedSSYT n ν) : BoundedSSYT (n + 1) μ :=
  ⟨{ entry := fun i j =>
       if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0
     row_weak' := fun {i j₁ j₂} hj hc => by
       by_cases hc₂ : ((i, j₂) : ℕ × ℕ) ∈ ν
       · have hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν := ν.up_left_mem le_rfl hj.le hc₂
         rw [if_pos hc₁, if_pos hc₂]
         exact T.1.row_weak hj hc₂
       · rw [if_neg hc₂, if_pos hc]
         by_cases hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν
         · rw [if_pos hc₁]
           exact (entry_lt T hc₁).le
         · rw [if_neg hc₁, if_pos (μ.up_left_mem le_rfl hj.le hc)]
     col_strict' := fun {i₁ i₂ j} hi hc => by
       have hc₁ : ((i₁, j) : ℕ × ℕ) ∈ ν := h.mem_of_lt hi hc
       rw [if_pos hc₁]
       by_cases hc₂ : ((i₂, j) : ℕ × ℕ) ∈ ν
       · rw [if_pos hc₂]
         exact T.1.col_strict hi hc₂
       · rw [if_neg hc₂, if_pos hc]
         exact entry_lt T hc₁
     zeros' := fun {_ _} hc => by
       rw [if_neg fun hν => hc (h.le hν), if_neg hc] },
    fun i j hc => by
      change (if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j
        else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0) < n + 1
      by_cases hc₁ : ((i, j) : ℕ × ℕ) ∈ ν
      · rw [if_pos hc₁]
        exact Nat.lt_succ_of_lt (entry_lt T hc₁)
      · rw [if_neg hc₁, if_pos hc]
        exact Nat.lt_succ_self n⟩

/-- The entries of an extended tableau. -/
@[simp]
theorem extend_apply (h : YoungDiagram.Interlaces ν μ) (T : BoundedSSYT n ν) (i j : ℕ) :
    (extend h T).1 i j =
      if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0 :=
  (rfl)

/-- Restoring the top letter on the cells of `μ / ν` gives back `ν` as the sub-shape of small
entries. -/
theorem restrictShape_extend (h : YoungDiagram.Interlaces ν μ) (T : BoundedSSYT n ν) :
    restrictShape (extend h T) = ν := by
  refine _root_.YoungDiagram.ext (Finset.ext fun c => ?_)
  obtain ⟨i, j⟩ := c
  simp only [_root_.YoungDiagram.mem_cells, mem_restrictShape, extend_apply]
  constructor
  · rintro ⟨hμ, hlt⟩
    by_contra hν
    rw [if_neg hν, if_pos hμ] at hlt
    exact absurd hlt (lt_irrefl n)
  · intro hν
    exact ⟨h.le hν, by rw [if_pos hν]; exact entry_lt T hν⟩

/-- **The branching bijection, fibrewise.**  The tableaux of shape `μ` in the letters `{0, …, n}`
whose sub-shape of small entries is a given `ν` are exactly the tableaux of shape `ν` in the
letters `{0, …, n - 1}`: erasing and restoring the top letter are mutually inverse. -/
def fiberEquiv (h : YoungDiagram.Interlaces ν μ) :
    {T : BoundedSSYT (n + 1) μ // restrictShape T = ν} ≃ BoundedSSYT n ν where
  toFun T := restrict T.1 ν T.2
  invFun T := ⟨extend h T, restrictShape_extend h T⟩
  left_inv := by
    rintro ⟨T, hT⟩
    refine Subtype.ext (Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_))
    rw [extend_apply, restrict_apply]
    by_cases hν : ((i, j) : ℕ × ℕ) ∈ ν
    · rw [if_pos hν, if_pos hν]
    · rw [if_neg hν]
      by_cases hμ : ((i, j) : ℕ × ℕ) ∈ μ
      · rw [if_pos hμ]
        have hnot : ¬ T.1 i j < n := fun hlt => hν ((mem_iff_of_restrictShape_eq hT).mpr ⟨hμ, hlt⟩)
        have hlt := entry_lt T hμ
        exact (show T.1 i j = n by omega).symm
      · rw [if_neg hμ]
        exact (T.1.zeros hμ).symm
  right_inv := by
    intro T
    refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
    rw [restrict_apply, extend_apply]
    by_cases hν : ((i, j) : ℕ × ℕ) ∈ ν
    · rw [if_pos hν, if_pos hν]
    · rw [if_neg hν]
      exact (T.1.zeros hν).symm

/-- **The branching decomposition of a sum over tableaux**: summing over the tableaux of shape `μ`
in the letters `{0, …, n}` is summing, over the shapes `ν` interlacing `μ` with at most `n` rows,
over the tableaux of shape `ν` in the letters `{0, …, n - 1}`. -/
theorem sum_eq_sum_interlacingShapes {M : Type*} [AddCommMonoid M] (n : ℕ)
    (μ : _root_.YoungDiagram) (f : ∀ ν : _root_.YoungDiagram, BoundedSSYT n ν → M) :
    ∑ ν ∈ YoungDiagram.interlacingShapes n μ, ∑ T : BoundedSSYT n ν, f ν T
      = ∑ T : BoundedSSYT (n + 1) μ, f (restrictShape T) (restrict T (restrictShape T) rfl) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun T _ => restrictShape_mem_interlacingShapes T)
    (fun T => f (restrictShape T) (restrict T (restrictShape T) rfl))]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [Finset.sum_subtype (p := fun T : BoundedSSYT (n + 1) μ => restrictShape T = ν) _
    (fun T => by simp)]
  refine (Fintype.sum_equiv (fiberEquiv (YoungDiagram.mem_interlacingShapes.mp hν).1) _ _
    fun T => ?_).symm
  obtain ⟨T, hT⟩ := T
  subst hT
  rfl

/-- **The branching rule for the number of tableaux**: the tableaux of shape `μ` in `n + 1` letters
are counted by the tableaux of the shapes interlacing `μ`, written in `n` letters.  This is the
counting shadow of the multiplicity-free `GLₙ₊₁ ↓ GLₙ` branching of irreducible
representations. -/
theorem card_eq_sum_interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram) :
    Fintype.card (BoundedSSYT (n + 1) μ)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, Fintype.card (BoundedSSYT n ν) := by
  simpa using (sum_eq_sum_interlacingShapes n μ fun _ _ => (1 : ℕ)).symm

end BoundedSSYT

end TauCeti
