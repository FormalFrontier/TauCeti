/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.KnotTheory.Grid.Diagram.Components
public import TauCeti.KnotTheory.Grid.Grading.Integer
public import TauCeti.KnotTheory.Grid.StateCardinality
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The standard unknot grid diagram of arbitrary grid number

This file builds the standard unknot grid diagram of every grid number `n + 2`: the `O` markings
sit on the diagonal and the `X` markings sit on the diagonal shifted up by one row, so the
represented link is the staircase closing up once around the torus in each direction, that is,
the unknot. Its smallest member, the `2 × 2` diagram `TauCeti.GridDiagram.twoByTwo`, is defined
here too and identified with the `n = 0` member of the family; the two-by-two grading
computations that use it live downstream in `TauCeti.KnotTheory.Grid.SmallGrid.Gradings`.

Two things are proved about the family. First it really is a knot diagram: its component
permutation is `(finRotate (n + 2))⁻¹`, a single `(n + 2)`-cycle, so all `n + 2` markings lie on
one component. Second, the bigradings of its two marking states are computed. Writing
`N = n + 2` for the grid number, the general lemmas `maslovOℤ_O` and `maslovXℤ_X` give
`M_O(O) = 1` and `M_X(X) = 1`, while the two crossed Maslov gradings are computed here to be
`M_X(O) = M_O(X) = N`. Hence

`(M_O, A)` is `(1, -(N - 1))` at the `O`-state and `(N, 0)` at the `X`-state.

Both gradings therefore differ by `N - 1` between the two marking states, which is the spread
expected of the fully blocked grid homology `GH̃` of an `N`-grid unknot: that homology is
predicted to be `W^{⊗(N-1)}` with `W = 𝔽 ⊕ 𝔽` in bigradings `(0, 0)` and `(-1, -1)`.
Nothing about the homology is proved here, and the gradings of the remaining grid states are
not compared with these two: only the two marking states are graded.

The Maslov computation reduces to four counts of pairs of columns, and each of the three crossed
counts differs from the plain count `#{(c, c') | c < c'}` by exactly `N - 1`; the missing pairs
are the ones ending in the last column, respectively the ones with consecutive columns. The three
count comparisons are the private lemmas below, and the plain count itself never has to be
evaluated.

## Main definitions

* `TauCeti.GridDiagram.unknot`: the standard unknot grid diagram of grid number `n + 2`.
* `TauCeti.GridDiagram.twoByTwo`: the standard `2 × 2` grid diagram, with `O` markings on the
  identity state and `X` markings on the transposition state.

## Main results

* `TauCeti.GridDiagram.unknot_zero`: in grid number two this is the diagram `twoByTwo`.
* `TauCeti.GridDiagram.componentPerm_unknot`, `TauCeti.GridDiagram.isKnot_unknot`,
  `TauCeti.GridDiagram.componentCycleType_unknot`: the diagram represents a knot, its component
  permutation being the inverse cyclic shift.
* `TauCeti.GridDiagram.relabelRows_relabelColumns_unknot`: the diagram is invariant under
  simultaneously shifting all rows and all columns by one, a cyclic symmetry of order `n + 2`.
* `TauCeti.GridDiagram.maslovXℤ_unknot_O` and `TauCeti.GridDiagram.maslovOℤ_unknot_X`: the two
  crossed Maslov gradings of the marking states are both the grid number.
* `TauCeti.GridDiagram.alexander_unknot_O` and `TauCeti.GridDiagram.alexander_unknot_X`: the
  Alexander gradings of the marking states are `-(n + 1)` and `0`.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.1, "Grid diagrams
and grid states", and supplies the diagram named in the acceptance criterion "`GH̃` of an
`n × n` unknot grid exhibits the `W^{⊗(n−1)}` factor". The diagram and the grading conventions
follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3 and 4.
-/

public section

namespace TauCeti

namespace GridDiagram

/-- The standard grid diagram for the unknot with grid number `n + 2`.

The `O` markings occupy the diagonal squares and the `X` markings the diagonal shifted up by one
row. Following the markings alternately horizontally and vertically traverses a single staircase
that winds once around the torus in each direction, so the represented link is the unknot. -/
def unknot (n : ℕ) : GridDiagram (n + 2) where
  O := ⟨1⟩
  X := ⟨finRotate (n + 2)⟩
  disjoint := by
    intro c h
    have hc : c ∈ Equiv.Perm.support (finRotate (n + 2)) := by simp
    exact Equiv.Perm.mem_support.mp hc (by simpa using h.symm)

variable (n : ℕ)

-- The body of `unknot` is deliberately not exposed, so the projection lemmas below are written
-- `(rfl)` rather than `rfl`: the parentheses opt out of exporting the definitional equality,
-- which downstream modules do not need and which the lemmas themselves replace.

/-- The `O` markings of the standard unknot grid are the identity permutation graph. -/
@[simp]
theorem unknot_O_toPerm : (unknot n).O.toPerm = 1 :=
  (rfl)

/-- The `X` markings of the standard unknot grid are the cyclic shift permutation graph. -/
@[simp]
theorem unknot_X_toPerm : (unknot n).X.toPerm = finRotate (n + 2) :=
  (rfl)

/-- The `O` marking of the standard unknot grid in a column is in the diagonal row. -/
theorem unknot_O_apply (c : Fin (n + 2)) : (unknot n).O c = c :=
  (rfl)

/-- The `X` marking of the standard unknot grid in a column is one row above the diagonal. -/
theorem unknot_X_apply (c : Fin (n + 2)) : (unknot n).X c = finRotate (n + 2) c :=
  (rfl)

/-- The `X` markings of the standard unknot grid form the shifted diagonal. -/
theorem unknot_X_apply_eq_add_one (c : Fin (n + 2)) : (unknot n).X c = c + 1 := by
  rw [unknot_X_apply]
  exact finRotate_apply c

/-! ### The smallest member, in grid number two -/

/-- The standard `2 × 2` grid diagram with `O` markings on the identity state and `X`
markings on the transposition state. This is the usual smallest grid diagram for the unknot. -/
abbrev twoByTwo : GridDiagram 2 where
  O := GridState.twoByTwoId
  X := GridState.twoByTwoSwap
  disjoint := by
    intro c h
    fin_cases c <;> simp at h

/-- The `O`-marking state of the standard two-by-two diagram is the identity state. -/
@[simp]
theorem twoByTwo_O : twoByTwo.O = GridState.twoByTwoId :=
  rfl

/-- The `X`-marking state of the standard two-by-two diagram is the transposition state. -/
@[simp]
theorem twoByTwo_X : twoByTwo.X = GridState.twoByTwoSwap :=
  rfl

/-- In grid number two the standard unknot grid is the `2 × 2` diagram `twoByTwo`. -/
theorem unknot_zero : unknot 0 = twoByTwo := by
  refine GridDiagram.ext rfl (GridState.ext fun c => ?_)
  revert c
  decide

/-! ### The represented link is a knot -/

/-- Traversing the standard unknot grid from an `O` marking to the `X` marking in its row and
back down to the next `O` marking shifts the column down by one. -/
theorem componentPerm_unknot : (unknot n).componentPerm = (finRotate (n + 2))⁻¹ := by
  refine Equiv.ext fun c => ?_
  rw [componentPerm_apply, unknot_O_apply]
  have h1 : (unknot n).X (XColumnOfRow (unknot n) c) = c := XColumnOfRow_apply _ c
  have h2 : (unknot n).X ((finRotate (n + 2))⁻¹ c) = c := by
    rw [unknot_X_apply]
    simp
  exact (unknot n).X.toPerm.injective (h1.trans h2.symm)

/-- The standard unknot grid diagram represents a knot: its component permutation is a single
cycle through all `n + 2` markings. -/
theorem isKnot_unknot : (unknot n).IsKnot := by
  rw [isKnot_iff_componentPerm_isCycle, componentPerm_unknot]
  exact isCycle_finRotate.inv

/-- The sole component of the standard unknot grid diagram carries all `n + 2` markings. -/
theorem componentCycleType_unknot : (unknot n).componentCycleType = {n + 2} :=
  (isKnot_unknot n).componentCycleType_eq

/-- The standard unknot grid diagram is invariant under shifting all rows and all columns by one
at the same time. This cyclic symmetry has order `n + 2`. -/
theorem relabelRows_relabelColumns_unknot :
    ((unknot n).relabelRows (finRotate (n + 2))).relabelColumns (finRotate (n + 2)) = unknot n := by
  refine GridDiagram.ext (GridState.ext fun c => ?_) (GridState.ext fun c => ?_)
  · rw [relabelColumns_O_apply, relabelRows_O_apply, unknot_O_apply, unknot_O_apply,
      Equiv.apply_symm_apply]
  · rw [relabelColumns_X_apply, relabelRows_X_apply, unknot_X_apply, unknot_X_apply,
      Equiv.apply_symm_apply]

/-! ### Column-pair counts for the Maslov gradings -/

/-- Splitting the pairs of columns in increasing order according to an auxiliary predicate. -/
private theorem card_filter_lt_split (P : Fin (n + 2) × Fin (n + 2) → Prop) [DecidablePred P] :
    (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) => p.1 < p.2 ∧ P p).card
        + (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) => p.1 < p.2 ∧ ¬ P p).card
      = (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) => p.1 < p.2).card := by
  rw [← Finset.filter_filter, ← Finset.filter_filter]
  exact Finset.card_filter_add_card_filter_not _

/-- A set of column pairs cut out by prescribing the second column as a function of the first,
which is required to avoid the last column, has `n + 1` elements. -/
private theorem card_filter_graph (f : Fin (n + 2) → Fin (n + 2)) :
    (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 ≠ Fin.last (n + 1) ∧ p.2 = f p.1).card = n + 1 := by
  have himg : (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 ≠ Fin.last (n + 1) ∧ p.2 = f p.1)
      = (Finset.univ.filter fun c : Fin (n + 2) => c ≠ Fin.last (n + 1)).image
          fun c => (c, f c) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨ha, rfl⟩
      exact ⟨a, ha, rfl, rfl⟩
    · rintro ⟨c, hc, rfl, rfl⟩
      exact ⟨hc, rfl⟩
  rw [himg, Finset.card_image_of_injective _ fun a b hab => congrArg Prod.fst hab,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- The number of increasing column pairs is unchanged by additionally demanding that the two
diagonal `O` markings be in increasing order, which they always are. -/
private theorem card_filter_lt_O_lt_O :
    (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 < p.2 ∧ (unknot n).O p.1 < (unknot n).O p.2).card
      = (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) => p.1 < p.2).card :=
  congrArg Finset.card (Finset.filter_congr fun p _ => by simp)

/-- Among the increasing column pairs, exactly the `n + 1` pairs ending in the last column fail to
put the first diagonal `O` marking below the second shifted `X` marking. -/
private theorem card_filter_lt_O_lt_X :
    (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 < p.2 ∧ (unknot n).O p.1 < (unknot n).X p.2).card + (n + 1)
      = (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) => p.1 < p.2).card := by
  have hset : (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 < p.2 ∧ ¬ ((unknot n).O p.1 < (unknot n).X p.2))
      = Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 ≠ Fin.last (n + 1) ∧ p.2 = (fun _ => Fin.last (n + 1)) p.1 := by
    refine Finset.filter_congr fun p _ => ?_
    rw [unknot_O_apply, unknot_X_apply]
    constructor
    · rintro ⟨h1, h2⟩
      have hlast : p.2 = Fin.last (n + 1) := by
        by_contra hne
        exact h2 (h1.trans ((lt_finRotate_iff_ne_last p.2).mpr hne))
      exact ⟨Fin.ne_of_lt (hlast ▸ h1), hlast⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h2 ▸ Fin.lt_last_iff_ne_last.mpr h1, ?_⟩
      rw [h2, finRotate_last]
      exact Fin.not_lt_zero p.1
  have hcard := card_filter_graph n fun _ => Fin.last (n + 1)
  rw [← hset] at hcard
  have hsplit := card_filter_lt_split n fun p => (unknot n).O p.1 < (unknot n).X p.2
  omega

/-- Among the increasing column pairs, exactly the `n + 1` pairs of consecutive columns fail to
put the first shifted `X` marking below the second diagonal `O` marking. -/
private theorem card_filter_lt_X_lt_O :
    (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 < p.2 ∧ (unknot n).X p.1 < (unknot n).O p.2).card + (n + 1)
      = (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) => p.1 < p.2).card := by
  have hset : (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 < p.2 ∧ ¬ ((unknot n).X p.1 < (unknot n).O p.2))
      = Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 ≠ Fin.last (n + 1) ∧ p.2 = finRotate (n + 2) p.1 := by
    refine Finset.filter_congr fun p _ => ?_
    rw [unknot_O_apply, unknot_X_apply]
    constructor
    · rintro ⟨h1, h2⟩
      have hne : p.1 ≠ Fin.last (n + 1) := Fin.ne_of_lt (h1.trans_le (Fin.le_last p.2))
      refine ⟨hne, ?_⟩
      have hval : (finRotate (n + 2) p.1 : ℕ) = (p.1 : ℕ) + 1 := coe_finRotate_of_ne_last hne
      have h3 : (p.2 : ℕ) ≤ (p.1 : ℕ) + 1 := by
        rw [← hval]
        exact Fin.not_lt.mp h2
      have h4 : (p.1 : ℕ) < (p.2 : ℕ) := h1
      exact Fin.ext (by omega)
    · rintro ⟨h1, h2⟩
      rw [h2]
      exact ⟨(lt_finRotate_iff_ne_last p.1).mpr h1, lt_irrefl _⟩
  have hcard := card_filter_graph n (finRotate (n + 2))
  rw [← hset] at hcard
  have hsplit := card_filter_lt_split n fun p => (unknot n).X p.1 < (unknot n).O p.2
  omega

/-- Among the increasing column pairs, exactly the `n + 1` pairs ending in the last column fail to
keep the two shifted `X` markings in increasing order. -/
private theorem card_filter_lt_X_lt_X :
    (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 < p.2 ∧ (unknot n).X p.1 < (unknot n).X p.2).card + (n + 1)
      = (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) => p.1 < p.2).card := by
  have hset : (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 < p.2 ∧ ¬ ((unknot n).X p.1 < (unknot n).X p.2))
      = Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 2) =>
        p.1 ≠ Fin.last (n + 1) ∧ p.2 = (fun _ => Fin.last (n + 1)) p.1 := by
    refine Finset.filter_congr fun p _ => ?_
    rw [unknot_X_apply, unknot_X_apply]
    constructor
    · rintro ⟨h1, h2⟩
      have hne1 : p.1 ≠ Fin.last (n + 1) := Fin.ne_of_lt (h1.trans_le (Fin.le_last p.2))
      have hlast : p.2 = Fin.last (n + 1) := by
        by_contra hne2
        refine h2 ?_
        rw [Fin.lt_def, coe_finRotate_of_ne_last hne1, coe_finRotate_of_ne_last hne2]
        exact Nat.succ_lt_succ h1
      exact ⟨hne1, hlast⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h2 ▸ Fin.lt_last_iff_ne_last.mpr h1, ?_⟩
      rw [h2, finRotate_last]
      exact Fin.not_lt_zero _
  have hcard := card_filter_graph n fun _ => Fin.last (n + 1)
  rw [← hset] at hcard
  have hsplit := card_filter_lt_split n fun p => (unknot n).X p.1 < (unknot n).X p.2
  omega

/-! ### The bigradings of the two marking states -/

/-- The `X`-Maslov grading of the `O`-marking state of the standard unknot grid is the grid
number. -/
theorem maslovXℤ_unknot_O : (unknot n).maslovXℤ (unknot n).O = n + 2 := by
  rw [maslovXℤ_eq_card]
  have h1 := card_filter_lt_O_lt_O n
  have h2 := card_filter_lt_O_lt_X n
  have h3 := card_filter_lt_X_lt_O n
  have h4 := card_filter_lt_X_lt_X n
  omega

/-- The `O`-Maslov grading of the `X`-marking state of the standard unknot grid is the grid
number. Swapping the roles of the two marking states turns the count computed in
`maslovXℤ_unknot_O` into this one, so no column-pair count has to be redone. -/
theorem maslovOℤ_unknot_X : (unknot n).maslovOℤ (unknot n).X = n + 2 := by
  have h := maslovXℤ_unknot_O n
  rw [maslovXℤ_eq_card] at h
  rw [maslovOℤ_eq_card]
  omega

/-- Twice the Alexander grading of the `X`-marking state of the standard unknot grid vanishes. -/
theorem alexanderTwoℤ_unknot_X : (unknot n).alexanderTwoℤ (unknot n).X = 0 := by
  rw [alexanderTwoℤ_def, maslovOℤ_unknot_X, maslovXℤ_X]
  push_cast
  ring

/-- Twice the Alexander grading of the `O`-marking state of the standard unknot grid is
`-2 (n + 1)`. -/
theorem alexanderTwoℤ_unknot_O : (unknot n).alexanderTwoℤ (unknot n).O = -2 * (n + 1) := by
  rw [alexanderTwoℤ_def, maslovOℤ_O, maslovXℤ_unknot_O]
  push_cast
  ring

/-- The Alexander grading of the `X`-marking state of the standard unknot grid is zero. -/
theorem alexander_unknot_X : (unknot n).alexander (unknot n).X = 0 := by
  have h := (unknot n).two_mul_alexander_eq_intCast (unknot n).X
  rw [alexanderTwoℤ_unknot_X] at h
  push_cast at h
  linarith

/-- The Alexander grading of the `O`-marking state of the standard unknot grid is `-(n + 1)`,
one less than the negated grid number. -/
theorem alexander_unknot_O : (unknot n).alexander (unknot n).O = -(n + 1) := by
  have h := (unknot n).two_mul_alexander_eq_intCast (unknot n).O
  rw [alexanderTwoℤ_unknot_O] at h
  push_cast at h
  linarith

end GridDiagram

end TauCeti
