/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Sym.Sym2

import Mathlib.Data.Sym.Card

/-!
# Grid diagrams and grid states

This file starts the grid-combinatorial lane of the Heegaard Floer roadmap. A grid state of
grid number `n` is a wrapper around a permutation of `Fin n`, sending each column to the
unique row occupied by the state in that column. A grid diagram is encoded by two such
permutation graphs, one for the `O` markings and one for the `X` markings, with the condition
that no square contains both markings.

The point-set API records the basic row, column, cardinality, and disjointness facts used
before defining rectangles, empty rectangles, and the grid differential.

* `TauCeti.GridState`: a grid state with a permutation graph on `Fin n`.
* `TauCeti.GridState.pointSet`: the finite set of occupied squares of a grid state.
* `TauCeti.GridDiagram`: an `n × n` grid diagram with `O` and `X` markings.
* `TauCeti.GridDiagram.OSet`, `TauCeti.GridDiagram.XSet`: the marking point sets.
* Relabeling, swapping, transposition, and marking-swap operations for grid states and diagrams.

## References

This supplies the first prerequisite for the Tau Ceti Heegaard Floer roadmap,
`HeegaardFloer/README.md` in TauCetiRoadmap, Lane G.1, "Grid diagrams and grid states". The
encoding follows the standard grid-diagram convention from Ozsváth--Stipsicz--Szabó, *Grid
Homology for Knots and Links*, Chapter 3: one `O` and one `X` marking in each row and column,
and a grid state is one point in each row and column.
-/

@[expose] public section

namespace TauCeti

/-- A grid state on an `n × n` toroidal grid.

The field `toPerm` sends each column to its occupied row. The named wrapper gives grid states
their own preferred point-set API below, while still allowing direct access to the underlying
permutation when needed. -/
structure GridState (n : ℕ) where
  /-- The permutation sending each column to the occupied row in that column. -/
  toPerm : Equiv.Perm (Fin n)

namespace GridState

variable {n : ℕ}

/-- Grid states on an `n × n` grid are equivalent to permutations of the columns. -/
def equivPerm (n : ℕ) : GridState n ≃ Equiv.Perm (Fin n) where
  toFun x := x.toPerm
  invFun σ := ⟨σ⟩
  left_inv x := by cases x; rfl
  right_inv σ := rfl

/-- There are finitely many grid states of a fixed grid size. -/
instance : Fintype (GridState n) :=
  Fintype.ofEquiv (Equiv.Perm (Fin n)) (equivPerm n).symm

/-- Equality of grid states is decidable: a grid state is determined by its underlying
permutation, whose equality is decidable. This makes finite sets of grid states computable. -/
instance : DecidableEq (GridState n) := fun x y =>
  decidable_of_iff (x.toPerm = y.toPerm)
    ⟨fun h => by cases x; cases y; cases h; rfl, fun h => by rw [h]⟩

/-- Apply a grid state to a column to get its occupied row. -/
instance : CoeFun (GridState n) fun _ => Fin n → Fin n where
  coe x := x.toPerm

/-- The permutation associated to a grid state by `GridState.equivPerm`. -/
@[simp] theorem equivPerm_apply (x : GridState n) : equivPerm n x = x.toPerm := rfl

/-- The grid state associated to a permutation by the inverse of `GridState.equivPerm`. -/
theorem equivPerm_symm_apply (σ : Equiv.Perm (Fin n)) : (equivPerm n).symm σ = ⟨σ⟩ := rfl

/-- Evaluating a grid state obtained from a permutation gives the permutation value. -/
@[simp] theorem equivPerm_symm_apply_apply (σ : Equiv.Perm (Fin n)) (c : Fin n) :
    ((equivPerm n).symm σ : GridState n) c = σ c := rfl

/-- Grid states are extensional in their column-to-row functions. -/
@[ext]
theorem ext {x y : GridState n} (h : ∀ c : Fin n, x c = y c) : x = y := by
  cases x
  cases y
  congr
  ext c
  exact congrArg Fin.val (h c)

/-- The finite set of occupied squares of a grid state. The first coordinate is the column and
the second coordinate is the row. -/
def pointSet (x : GridState n) : Finset (Fin n × Fin n) :=
  Finset.univ.image fun c => (c, x c)

/-- The point set of the grid state obtained from `σ` is the graph `{(c, σ c)}`. -/
@[simp] theorem equivPerm_symm_pointSet (σ : Equiv.Perm (Fin n)) :
    ((equivPerm n).symm σ : GridState n).pointSet = Finset.univ.image fun c => (c, σ c) := rfl

/-- Membership in the point set of a grid state is the graph condition for its permutation. -/
@[simp]
theorem mem_pointSet (x : GridState n) (p : Fin n × Fin n) :
    p ∈ x.pointSet ↔ x p.1 = p.2 := by
  constructor
  · intro hp
    rw [pointSet] at hp
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hp
    rw [← Prod.mk.inj hc |>.1]
    exact Prod.mk.inj hc |>.2
  · intro hp
    rw [pointSet]
    exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, by ext <;> simp [hp]⟩

/-- The square `(c, r)` lies in a grid state's point set exactly when `x c = r`. -/
theorem mk_mem_pointSet (x : GridState n) (c r : Fin n) : (c, r) ∈ x.pointSet ↔ x c = r := by
  simp

/-- The point set of a grid state has exactly `n` occupied squares. -/
@[simp]
theorem card_pointSet (x : GridState n) : x.pointSet.card = n := by
  rw [pointSet, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fin]
  · intro a b hab
    exact Prod.mk.inj hab |>.1

/-- A grid state has a unique occupied row in each column. -/
theorem existsUnique_row_of_column (x : GridState n) (c : Fin n) :
    ∃! r : Fin n, (c, r) ∈ x.pointSet := by
  refine ⟨x c, by simp, ?_⟩
  intro r hr
  exact ((mk_mem_pointSet x c r).mp hr).symm

/-- A grid state has a unique occupied column in each row. -/
theorem existsUnique_column_of_row (x : GridState n) (r : Fin n) :
    ∃! c : Fin n, (c, r) ∈ x.pointSet := by
  refine ⟨x.toPerm.symm r, by simp, ?_⟩
  intro c hc
  exact x.toPerm.injective (by simpa using hc)

/-- The column occupied by a grid state in a given row. -/
def columnOfRow (x : GridState n) (r : Fin n) : Fin n :=
  x.toPerm.symm r

/-- The point in row `r` lies in column `columnOfRow x r`. -/
theorem apply_columnOfRow (x : GridState n) (r : Fin n) : x (x.columnOfRow r) = r := by
  simp [columnOfRow]

/-- The column containing the point in row `x c` is `c`. -/
theorem columnOfRow_apply (x : GridState n) (c : Fin n) : x.columnOfRow (x c) = c := by
  simp [columnOfRow]

/-- Point sets of grid states are equal exactly when the underlying permutations are equal. -/
@[simp]
theorem pointSet_inj {x y : GridState n} : x.pointSet = y.pointSet ↔ x = y := by
  constructor
  · intro h
    ext c
    have hx : (c, x c) ∈ y.pointSet := by simpa [h] using mk_mem_pointSet x c (x c) |>.mpr rfl
    exact congrArg Fin.val ((mk_mem_pointSet y c (x c)).mp hx).symm
  · intro h
    simp [h]

/-- A square lies in both state point sets exactly when both state permutations send its
column to its row. -/
theorem mem_pointSet_inter (x y : GridState n) (p : Fin n × Fin n) :
    p ∈ x.pointSet ∩ y.pointSet ↔ x p.1 = p.2 ∧ y p.1 = p.2 := by
  simp

/-- Two grid states have disjoint point sets exactly when they disagree in every column. -/
theorem disjoint_pointSet_iff (x y : GridState n) :
    Disjoint x.pointSet y.pointSet ↔ ∀ c : Fin n, x c ≠ y c := by
  rw [Finset.disjoint_iff_ne]
  constructor
  · intro h c hxy
    exact h (c, x c) (by simp) (c, x c) (by simp [hxy]) rfl
  · intro h p hpX q hpY hpq
    subst hpq
    exact h p.1 ((mem_pointSet x p).mp hpX |>.trans ((mem_pointSet y p).mp hpY).symm)

/-- Relabel the rows of a grid state by a permutation of `Fin n`.

If `ρ` is the row permutation, the point in column `c` moves from row `x c` to row
`ρ (x c)`. -/
def relabelRows (ρ : Equiv.Perm (Fin n)) (x : GridState n) : GridState n where
  toPerm :=
    { toFun := fun c => ρ (x c)
      invFun := fun r => x.toPerm.symm (ρ.symm r)
      left_inv := by
        intro c
        simp
      right_inv := by
        intro r
        simp }

/-- Relabel the columns of a grid state by a permutation of `Fin n`.

The point in the old column `c` appears in the new column `κ c`, so the row in a new column
`c` is read from the old column `κ.symm c`. -/
def relabelColumns (κ : Equiv.Perm (Fin n)) (x : GridState n) : GridState n where
  toPerm :=
    { toFun := fun c => x (κ.symm c)
      invFun := fun r => κ (x.toPerm.symm r)
      left_inv := by
        intro c
        simp
      right_inv := by
        intro r
        simp }

/-- Row relabeling evaluates by applying the row permutation to the old row. -/
@[simp]
theorem relabelRows_apply (ρ : Equiv.Perm (Fin n)) (x : GridState n) (c : Fin n) :
    x.relabelRows ρ c = ρ (x c) :=
  rfl

/-- Column relabeling evaluates by reading the old state at the inverse column. -/
@[simp]
theorem relabelColumns_apply (κ : Equiv.Perm (Fin n)) (x : GridState n) (c : Fin n) :
    x.relabelColumns κ c = x (κ.symm c) :=
  rfl

/-- Relabeling rows by the identity permutation does not change a grid state. -/
@[simp]
theorem relabelRows_refl (x : GridState n) : x.relabelRows (Equiv.refl (Fin n)) = x := by
  ext c
  simp

/-- Relabeling columns by the identity permutation does not change a grid state. -/
@[simp]
theorem relabelColumns_refl (x : GridState n) :
    x.relabelColumns (Equiv.refl (Fin n)) = x := by
  ext c
  simp

/-- Successive row relabelings compose. -/
@[simp]
theorem relabelRows_relabelRows (ρ σ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelRows ρ).relabelRows σ = x.relabelRows (ρ.trans σ) := by
  ext c
  simp

/-- Successive column relabelings compose. -/
@[simp]
theorem relabelColumns_relabelColumns (κ τ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelColumns κ).relabelColumns τ = x.relabelColumns (κ.trans τ) := by
  ext c
  simp

/-- Row and column relabeling commute on grid states. -/
theorem relabelRows_relabelColumns (ρ κ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelRows ρ).relabelColumns κ = (x.relabelColumns κ).relabelRows ρ := by
  ext c
  simp

/-- Membership in the point set after a row relabeling. -/
theorem mem_pointSet_relabelRows (ρ : Equiv.Perm (Fin n)) (x : GridState n) (p : Fin n × Fin n) :
    p ∈ (x.relabelRows ρ).pointSet ↔ (p.1, ρ.symm p.2) ∈ x.pointSet := by
  simp only [mem_pointSet, relabelRows_apply]
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [h]
    simp

/-- Membership in the point set after a column relabeling. -/
theorem mem_pointSet_relabelColumns (κ : Equiv.Perm (Fin n)) (x : GridState n) (p : Fin n × Fin n) :
    p ∈ (x.relabelColumns κ).pointSet ↔ (κ.symm p.1, p.2) ∈ x.pointSet := by
  simp

/-- Swapping two rows in a grid state. -/
def swapRows (a b : Fin n) (x : GridState n) : GridState n :=
  x.relabelRows (Equiv.swap a b)

/-- Swapping two columns in a grid state. -/
def swapColumns (a b : Fin n) (x : GridState n) : GridState n :=
  x.relabelColumns (Equiv.swap a b)

/-- Row swaps evaluate by swapping the row selected by the old state. -/
@[simp]
theorem swapRows_apply (a b : Fin n) (x : GridState n) (c : Fin n) :
    x.swapRows a b c = Equiv.swap a b (x c) :=
  rfl

/-- Column swaps evaluate by reading the old state at the swapped column. -/
@[simp]
theorem swapColumns_apply (a b : Fin n) (x : GridState n) (c : Fin n) :
    x.swapColumns a b c = x (Equiv.swap a b c) := by
  simp [swapColumns, relabelColumns]

/-- Swapping columns is symmetric in the two chosen columns. -/
theorem swapColumns_comm (a b : Fin n) (x : GridState n) :
    x.swapColumns a b = x.swapColumns b a := by
  ext c
  simp [swapColumns_apply, Equiv.swap_comm]

/-- Swapping the same pair of columns twice is the identity on grid states. -/
@[simp]
theorem swapColumns_swapColumns (a b : Fin n) (x : GridState n) :
    (x.swapColumns a b).swapColumns a b = x := by
  ext c
  simp [swapColumns]

/-- The grid states obtained from `x` by transposing a pair of distinct columns.

These are exactly the states a single grid rectangle can reach from `x`: the fully blocked
differential of the generator `x` is supported here. -/
def columnSwapNeighbors (x : GridState n) : Finset (GridState n) :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2).image
    fun p => x.swapColumns p.1 p.2

/-- A state is a column-swap neighbour of `x` exactly when it is `x` with a pair of distinct
columns transposed. -/
@[simp]
theorem mem_columnSwapNeighbors {x y : GridState n} :
    y ∈ x.columnSwapNeighbors ↔ ∃ c d : Fin n, c ≠ d ∧ y = x.swapColumns c d := by
  simp only [columnSwapNeighbors, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists]
  constructor
  · rintro ⟨c, d, hcd, rfl⟩
    exact ⟨c, d, hcd, rfl⟩
  · rintro ⟨c, d, hcd, rfl⟩
    exact ⟨c, d, hcd, rfl⟩

/-- If `y` is a column-swap neighbour of `x`, then `x` is a column-swap neighbour of `y`.

This is the elementary reversibility of a rectangle target: the same pair of side columns swaps
back to the source state. -/
theorem mem_columnSwapNeighbors_comm {x y : GridState n} :
    y ∈ x.columnSwapNeighbors ↔ x ∈ y.columnSwapNeighbors := by
  constructor
  · rw [mem_columnSwapNeighbors]
    rintro ⟨a, b, hab, rfl⟩
    rw [mem_columnSwapNeighbors]
    refine ⟨a, b, hab, ?_⟩
    exact (GridState.swapColumns_swapColumns a b x).symm
  · rw [mem_columnSwapNeighbors]
    rintro ⟨a, b, hab, hxy⟩
    rw [mem_columnSwapNeighbors]
    refine ⟨a, b, hab, ?_⟩
    rw [hxy]
    exact (GridState.swapColumns_swapColumns a b y).symm

/-- The finite set of column-swap neighbours is the image of the off-diagonal of the
column set: an ordered pair of distinct columns gives the state obtained by swapping
those columns. -/
theorem columnSwapNeighbors_eq_offDiag_image (x : GridState n) :
    x.columnSwapNeighbors =
      (Finset.univ : Finset (Fin n)).offDiag.image fun p => x.swapColumns p.1 p.2 := by
  ext y
  simp [columnSwapNeighbors, Finset.mem_offDiag]

/-- If two nontrivial column swaps of the same grid state agree, then they swap the same
unordered pair of columns. -/
theorem sym2_mk_eq_of_swapColumns_eq {x : GridState n} {a b c d : Fin n} (hab : a ≠ b)
    (hcd : c ≠ d) (h : x.swapColumns a b = x.swapColumns c d) : s(a, b) = s(c, d) := by
  have hswap : Equiv.swap a b = Equiv.swap c d := by
    ext k
    apply congrArg Fin.val
    exact x.toPerm.injective
      (by simpa [swapColumns_apply] using congrArg (fun y : GridState n => y k) h)
  have ha : a = c ∨ a = d := by
    by_contra hnot
    rw [not_or] at hnot
    have hval := congrArg (fun e : Equiv.Perm (Fin n) => e a) hswap
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hnot.1 hnot.2] at hval
    exact hab hval.symm
  rcases ha with rfl | rfl
  · have hbd : b = d := by
      simpa using congrArg (fun e : Equiv.Perm (Fin n) => e a) hswap
    rw [hbd]
  · have hbc : b = c := by
      simpa using congrArg (fun e : Equiv.Perm (Fin n) => e a) hswap
    rw [hbc, Sym2.eq_swap]

/-- The map from unordered off-diagonal column pairs to the state obtained by swapping those
columns is injective on the off-diagonal image. -/
private theorem injOn_sym2_lift_swapColumns_offDiag (x : GridState n) :
    Set.InjOn
      (Sym2.lift
        ⟨fun a b => x.swapColumns a b, fun a b => by
          ext c
          simp [swapColumns, Equiv.swap_comm]⟩)
      ((((Finset.univ : Finset (Fin n)).offDiag.image Sym2.mk.uncurry) :
        Set (Sym2 (Fin n)))) := by
  intro z hz w hw hzw
  obtain ⟨⟨a, b⟩, hab, hgz⟩ := Finset.mem_image.mp hz
  obtain ⟨⟨c, d⟩, hcd, hgw⟩ := Finset.mem_image.mp hw
  rw [← hgz, ← hgw] at hzw ⊢
  exact sym2_mk_eq_of_swapColumns_eq (x := x) (by simpa [Finset.mem_offDiag] using hab)
    (by simpa [Finset.mem_offDiag] using hcd)
    (by
      simpa using hzw)

/-- A grid state has exactly `n.choose 2` column-swap neighbours. -/
@[simp]
theorem card_columnSwapNeighbors (x : GridState n) :
    x.columnSwapNeighbors.card = n.choose 2 := by
  classical
  let pairSwap : Sym2 (Fin n) → GridState n :=
    Sym2.lift
      ⟨fun a b => x.swapColumns a b, fun a b => by
        ext c
        simp [swapColumns, Equiv.swap_comm]⟩
  have hpairSwap_injOn :
      Set.InjOn pairSwap
        (((Finset.univ : Finset (Fin n)).offDiag.image Sym2.mk.uncurry) :
          Set (Sym2 (Fin n))) := by
    simpa [pairSwap] using injOn_sym2_lift_swapColumns_offDiag x
  have himage :
      x.columnSwapNeighbors =
        ((Finset.univ : Finset (Fin n)).offDiag.image Sym2.mk.uncurry).image pairSwap := by
    ext y
    constructor
    · intro hy
      rw [mem_columnSwapNeighbors] at hy
      obtain ⟨a, b, hab, rfl⟩ := hy
      exact Finset.mem_image.mpr
        ⟨s(a, b), Finset.mem_image.mpr ⟨(a, b), by simpa [Finset.mem_offDiag], rfl⟩, rfl⟩
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
      rw [mem_columnSwapNeighbors]
      exact ⟨a, b, by simpa [Finset.mem_offDiag] using hab, rfl⟩
  calc
    x.columnSwapNeighbors.card =
        (((Finset.univ : Finset (Fin n)).offDiag.image Sym2.mk.uncurry).image pairSwap).card :=
      congrArg Finset.card himage
    _ = ((Finset.univ : Finset (Fin n)).offDiag.image Sym2.mk.uncurry).card :=
      Finset.card_image_of_injOn hpairSwap_injOn
    _ = n.choose 2 := by rw [Sym2.card_image_offDiag, Finset.card_univ, Fintype.card_fin]

/-- A grid state has at most `n.choose 2` column-swap neighbours. -/
theorem card_columnSwapNeighbors_le (x : GridState n) :
    x.columnSwapNeighbors.card ≤ n.choose 2 := by
  rw [x.card_columnSwapNeighbors]

/-- A grid state on a grid of size at most `1` has no column-swap neighbours. -/
theorem columnSwapNeighbors_eq_empty_of_le_one (x : GridState n) (hn : n ≤ 1) :
    x.columnSwapNeighbors = ∅ := by
  have hchoose : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le hn)
  apply Finset.card_eq_zero.mp
  exact Nat.eq_zero_of_le_zero ((x.card_columnSwapNeighbors_le).trans (by rw [hchoose]))

/-- A grid state on a grid of size `0` has no column-swap neighbours. -/
@[simp]
theorem columnSwapNeighbors_eq_empty_of_zero (x : GridState 0) :
    x.columnSwapNeighbors = ∅ :=
  x.columnSwapNeighbors_eq_empty_of_le_one (Nat.zero_le 1)

/-- A grid state on a grid of size `1` has no column-swap neighbours. -/
@[simp]
theorem columnSwapNeighbors_eq_empty_of_one (x : GridState 1) :
    x.columnSwapNeighbors = ∅ :=
  x.columnSwapNeighbors_eq_empty_of_le_one le_rfl

/-- A grid state is not a column-swap neighbour of itself: swapping two distinct columns moves the
occupied row of either column, so the result differs from the original. -/
theorem self_notMem_columnSwapNeighbors (x : GridState n) : x ∉ x.columnSwapNeighbors := by
  rw [mem_columnSwapNeighbors]
  rintro ⟨c, d, hcd, hx⟩
  have hval := congrArg (fun z : GridState n => z c) hx
  simp only [swapColumns_apply, Equiv.swap_apply_left] at hval
  exact hcd (x.toPerm.injective hval)

/-- Row swaps transport the point set by the row transposition. -/
theorem mem_pointSet_swapRows (a b : Fin n) (x : GridState n) (p : Fin n × Fin n) :
    p ∈ (x.swapRows a b).pointSet ↔ (p.1, Equiv.swap a b p.2) ∈ x.pointSet := by
  simpa [swapRows] using GridState.mem_pointSet_relabelRows (Equiv.swap a b) x p

/-- Column swaps transport the point set by the column transposition. -/
theorem mem_pointSet_swapColumns (a b : Fin n) (x : GridState n) (p : Fin n × Fin n) :
    p ∈ (x.swapColumns a b).pointSet ↔ (Equiv.swap a b p.1, p.2) ∈ x.pointSet := by
  simp [swapColumns]

/-- A square is shared by a grid state and a column relabeling exactly when it is a
source-state square whose column is fixed by the relabeling permutation. -/
theorem mem_pointSet_inter_relabelColumns_iff (x : GridState n) (κ : Equiv.Perm (Fin n))
    (p : Fin n × Fin n) :
    p ∈ x.pointSet ∩ (x.relabelColumns κ).pointSet ↔ p ∈ x.pointSet ∧ κ p.1 = p.1 := by
  rw [Finset.mem_inter, mem_pointSet_relabelColumns]
  constructor
  · rintro ⟨hx, hκ⟩
    refine ⟨hx, ?_⟩
    have hx_col : x p.1 = p.2 := (mem_pointSet x p).mp hx
    have hκ_col : x (κ.symm p.1) = p.2 :=
      (mem_pointSet x (κ.symm p.1, p.2)).mp hκ
    have hfixed_symm : κ.symm p.1 = p.1 :=
      x.toPerm.injective (hκ_col.trans hx_col.symm)
    calc
      κ p.1 = κ (κ.symm p.1) := by rw [hfixed_symm]
      _ = p.1 := by simp
  · rintro ⟨hx, hfixed⟩
    refine ⟨hx, ?_⟩
    have hfixed_symm : κ.symm p.1 = p.1 := by
      apply κ.injective
      simp [hfixed]
    simpa [hfixed_symm] using hx

/-- Swapping the same pair of rows twice is the identity on grid states. -/
@[simp]
theorem swapRows_swapRows (a b : Fin n) (x : GridState n) : (x.swapRows a b).swapRows a b = x := by
  ext c
  simp [swapRows]

/-- A square is shared by a grid state and the state with columns `a` and `b` swapped exactly
when it is a source-state square away from the two swapped columns. -/
theorem mem_pointSet_inter_swapColumns_iff (x : GridState n) {a b : Fin n} (h : a ≠ b)
    (p : Fin n × Fin n) :
    p ∈ x.pointSet ∩ (x.swapColumns a b).pointSet ↔
      p ∈ x.pointSet ∧ p.1 ≠ a ∧ p.1 ≠ b := by
  rw [swapColumns, mem_pointSet_inter_relabelColumns_iff]
  constructor
  · rintro ⟨hx, hfixed⟩
    refine ⟨hx, ?_, ?_⟩
    · intro hpa
      rw [hpa, Equiv.swap_apply_left] at hfixed
      exact h hfixed.symm
    · intro hpb
      rw [hpb, Equiv.swap_apply_right] at hfixed
      exact h hfixed
  · rintro ⟨hx, ha, hb⟩
    exact ⟨hx, Equiv.swap_apply_of_ne_of_ne ha hb⟩

/-- The point set of a grid state is the shared part with a column swap, together with the two
source-state squares in the swapped columns. -/
theorem pointSet_eq_insert_insert_inter_swapColumns (x : GridState n) {a b : Fin n} (h : a ≠ b) :
    x.pointSet =
      insert (a, x a) (insert (b, x b) (x.pointSet ∩ (x.swapColumns a b).pointSet)) := by
  ext p
  simp only [Finset.mem_insert]
  constructor
  · intro hx
    rcases eq_or_ne p.1 a with ha | ha
    · refine Or.inl ?_
      have : p.2 = x a := by
        simpa [ha] using ((mem_pointSet x p).mp hx).symm
      exact Prod.ext ha this
    · rcases eq_or_ne p.1 b with hb | hb
      · refine Or.inr (Or.inl ?_)
        have : p.2 = x b := by
          simpa [hb] using ((mem_pointSet x p).mp hx).symm
        exact Prod.ext hb this
      · exact Or.inr (Or.inr ((mem_pointSet_inter_swapColumns_iff x h p).mpr ⟨hx, ha, hb⟩))
  · rintro (rfl | rfl | hp)
    · simp
    · simp
    · exact Finset.mem_of_mem_inter_left hp

/-- The point set after swapping columns `a` and `b` is the shared part with the source state,
together with the two target-state squares in the swapped columns. -/
theorem swapColumns_pointSet_eq_insert_insert_inter (x : GridState n) {a b : Fin n} (h : a ≠ b) :
    (x.swapColumns a b).pointSet =
      insert (a, x b) (insert (b, x a) (x.pointSet ∩ (x.swapColumns a b).pointSet)) := by
  ext p
  simp only [Finset.mem_insert]
  constructor
  · intro hp
    rcases eq_or_ne p.1 a with ha | ha
    · refine Or.inl ?_
      have : p.2 = x b := by
        simpa [ha] using ((mem_pointSet (x.swapColumns a b) p).mp hp).symm
      exact Prod.ext ha this
    · rcases eq_or_ne p.1 b with hb | hb
      · refine Or.inr (Or.inl ?_)
        have : p.2 = x a := by
          simpa [hb] using ((mem_pointSet (x.swapColumns a b) p).mp hp).symm
        exact Prod.ext hb this
      · refine Or.inr (Or.inr ?_)
        have hx : p ∈ x.pointSet := by
          rw [mem_pointSet] at hp ⊢
          rw [swapColumns_apply, Equiv.swap_apply_of_ne_of_ne ha hb] at hp
          exact hp
        exact (mem_pointSet_inter_swapColumns_iff x h p).mpr ⟨hx, ha, hb⟩
  · rintro (rfl | rfl | hp)
    · simp
    · simp
    · exact Finset.mem_of_mem_inter_right hp

/-- A grid state and a swap of two distinct columns share exactly `n - 2` squares. -/
theorem card_pointSet_inter_swapColumns (x : GridState n) {a b : Fin n} (h : a ≠ b) :
    (x.pointSet ∩ (x.swapColumns a b).pointSet).card = n - 2 := by
  have hne : (b, x b) ∉ x.pointSet ∩ (x.swapColumns a b).pointSet := by
    rw [mem_pointSet_inter_swapColumns_iff x h]
    rintro ⟨_, _, hb⟩
    exact hb rfl
  have hne' :
      (a, x a) ∉ insert (b, x b) (x.pointSet ∩ (x.swapColumns a b).pointSet) := by
    rw [Finset.mem_insert]
    rintro (hab | ha)
    · exact absurd (congrArg Prod.fst hab) h
    · rw [mem_pointSet_inter_swapColumns_iff x h] at ha
      exact ha.2.1 rfl
  have hcard := congrArg Finset.card (pointSet_eq_insert_insert_inter_swapColumns x h)
  rw [card_pointSet, Finset.card_insert_of_notMem hne',
    Finset.card_insert_of_notMem hne] at hcard
  omega

/-- The diagonal reflection of a grid state.

Reflecting the occupied squares across the main diagonal exchanges columns and rows, so the new
permutation graph is the inverse of the old one. -/
def transpose (x : GridState n) : GridState n where
  toPerm := x.toPerm.symm
/-- The diagonal reflection evaluates by the inverse permutation graph. -/
@[simp]
theorem transpose_apply (x : GridState n) (c : Fin n) : x.transpose c = x.toPerm.symm c :=
  rfl

/-- The row-to-column accessor is evaluation of the reflected grid state. -/
@[simp]
theorem columnOfRow_eq_transpose (x : GridState n) (r : Fin n) :
    x.columnOfRow r = x.transpose r := rfl
/-- The column in row `r` of the reflected state is the original row-coordinate value at `r`. -/
theorem columnOfRow_transpose (x : GridState n) (r : Fin n) : x.transpose.columnOfRow r = x r := by
  simp [columnOfRow, transpose]
/-- The diagonal reflection is an involution on grid states. -/
@[simp]
theorem transpose_transpose (x : GridState n) : x.transpose.transpose = x := by
  cases x
  simp [transpose]
/-- Reflecting after a row relabeling is the same as column relabeling after reflecting. -/
@[simp]
theorem relabelRows_transpose (ρ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelRows ρ).transpose = x.transpose.relabelColumns ρ := by
  ext c
  exact congrArg Fin.val <| by
    apply (x.relabelRows ρ).toPerm.injective
    simp
/-- Reflecting after a column relabeling is the same as row relabeling after reflecting. -/
@[simp]
theorem relabelColumns_transpose (κ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelColumns κ).transpose = x.transpose.relabelRows κ := by
  ext c
  exact congrArg Fin.val <| by
    apply (x.relabelColumns κ).toPerm.injective
    simp
/-- Reflecting after a row swap is the same as the corresponding column swap after reflecting. -/
@[simp]
theorem swapRows_transpose (a b : Fin n) (x : GridState n) :
    (x.swapRows a b).transpose = x.transpose.swapColumns a b := by
  simp [swapRows, swapColumns]
/-- Reflecting after a column swap is the same as the corresponding row swap after reflecting. -/
@[simp]
theorem swapColumns_transpose (a b : Fin n) (x : GridState n) :
    (x.swapColumns a b).transpose = x.transpose.swapRows a b := by
  simp [swapRows, swapColumns]

/-- A square lies in the reflected state exactly when its diagonal reflection lies in the
original state. -/
theorem mem_pointSet_transpose (x : GridState n) (p : Fin n × Fin n) :
    p ∈ x.transpose.pointSet ↔ Prod.swap p ∈ x.pointSet := by
  simp only [mem_pointSet, transpose_apply]
  rw [Equiv.symm_apply_eq, eq_comm]
  rfl

/-- The point set of the reflected state is the diagonal reflection of the original point set. -/
theorem transpose_pointSet (x : GridState n) :
    x.transpose.pointSet = x.pointSet.image Prod.swap := by
  ext p
  rw [mem_pointSet_transpose, Finset.mem_image]
  constructor
  · intro hp
    exact ⟨Prod.swap p, hp, Prod.swap_swap p⟩
  · rintro ⟨q, hq, rfl⟩
    rwa [Prod.swap_swap]

end GridState

/-- An `n × n` grid diagram, encoded by the `O`-marking and `X`-marking permutation graphs.

The permutation fields enforce one `O` and one `X` in each row and column. The `disjoint`
field says no square contains both markings. -/
@[ext]
structure GridDiagram (n : ℕ) where
  /-- The `O` marking in each column, encoded by its row. -/
  O : GridState n
  /-- The `X` marking in each column, encoded by its row. -/
  X : GridState n
  /-- No square contains both an `O` marking and an `X` marking. -/
  disjoint : ∀ c : Fin n, O c ≠ X c

/-- There is no grid diagram of size `1`: the unique `O` and `X` markings would have to
occupy the same square. -/
instance : IsEmpty (GridDiagram 1) where
  false := by
    intro G
    exact G.disjoint 0 (Subsingleton.elim _ _)

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The finite set of `O` markings of a grid diagram. The first coordinate is the column and
the second coordinate is the row. -/
def OSet : Finset (Fin n × Fin n) :=
  G.O.pointSet

/-- The finite set of `X` markings of a grid diagram. The first coordinate is the column and
the second coordinate is the row. -/
def XSet : Finset (Fin n × Fin n) :=
  G.X.pointSet

/-- Membership in the `O`-marking set is the graph condition for the `O` permutation. -/
@[simp]
theorem mem_OSet (p : Fin n × Fin n) : p ∈ G.OSet ↔ G.O p.1 = p.2 := by
  simp [OSet]

/-- Membership in the `X`-marking set is the graph condition for the `X` permutation. -/
@[simp]
theorem mem_XSet (p : Fin n × Fin n) : p ∈ G.XSet ↔ G.X p.1 = p.2 := by
  simp [XSet]

/-- The square `(c, r)` contains an `O` marking exactly when `G.O c = r`. -/
theorem mk_mem_OSet (c r : Fin n) : (c, r) ∈ G.OSet ↔ G.O c = r := by
  simp [OSet]

/-- The square `(c, r)` contains an `X` marking exactly when `G.X c = r`. -/
theorem mk_mem_XSet (c r : Fin n) : (c, r) ∈ G.XSet ↔ G.X c = r := by
  simp [XSet]

/-- A grid diagram has exactly `n` `O` markings. -/
@[simp]
theorem card_OSet : G.OSet.card = n := by
  simp [OSet]

/-- A grid diagram has exactly `n` `X` markings. -/
@[simp]
theorem card_XSet : G.XSet.card = n := by
  simp [XSet]

/-- A grid diagram has a unique `O` marking in each column. -/
theorem existsUnique_ORow_of_column (c : Fin n) :
    ∃! r : Fin n, (c, r) ∈ G.OSet := by
  rw [OSet]
  exact G.O.existsUnique_row_of_column c

/-- A grid diagram has a unique `X` marking in each column. -/
theorem existsUnique_XRow_of_column (c : Fin n) :
    ∃! r : Fin n, (c, r) ∈ G.XSet := by
  rw [XSet]
  exact G.X.existsUnique_row_of_column c

/-- A grid diagram has a unique `O` marking in each row. -/
theorem existsUnique_OColumn_of_row (r : Fin n) :
    ∃! c : Fin n, (c, r) ∈ G.OSet := by
  rw [OSet]
  exact G.O.existsUnique_column_of_row r

/-- A grid diagram has a unique `X` marking in each row. -/
theorem existsUnique_XColumn_of_row (r : Fin n) :
    ∃! c : Fin n, (c, r) ∈ G.XSet := by
  rw [XSet]
  exact G.X.existsUnique_column_of_row r

/-- The column containing the `O` marking in a given row. -/
def OColumnOfRow (r : Fin n) : Fin n :=
  G.O.columnOfRow r

/-- The column containing the `X` marking in a given row. -/
def XColumnOfRow (r : Fin n) : Fin n :=
  G.X.columnOfRow r

/-- The `O` marking in row `r` lies in column `OColumnOfRow r`. -/
@[simp]
theorem OColumnOfRow_apply (r : Fin n) : G.O (OColumnOfRow G r) = r := by
  simp [OColumnOfRow]

/-- The `X` marking in row `r` lies in column `XColumnOfRow r`. -/
@[simp]
theorem XColumnOfRow_apply (r : Fin n) : G.X (XColumnOfRow G r) = r := by
  simp [XColumnOfRow]

/-- The column containing the `O` marking in row `G.O c` is `c`. -/
@[simp]
theorem OColumnOfRow_O (c : Fin n) : OColumnOfRow G (G.O c) = c := by
  simp [OColumnOfRow]

/-- The column containing the `X` marking in row `G.X c` is `c`. -/
@[simp]
theorem XColumnOfRow_X (c : Fin n) : XColumnOfRow G (G.X c) = c := by
  simp [XColumnOfRow]

/-- The `O` and `X` marking sets of a grid diagram are disjoint. -/
theorem disjoint_OSet_XSet : Disjoint G.OSet G.XSet := by
  rw [OSet, XSet, GridState.disjoint_pointSet_iff]
  exact G.disjoint

/-- No square contains both an `O` marking and an `X` marking. -/
theorem not_mem_OSet_and_mem_XSet (p : Fin n × Fin n) : ¬ (p ∈ G.OSet ∧ p ∈ G.XSet) := by
  intro hp
  exact Finset.disjoint_left.mp G.disjoint_OSet_XSet hp.1 hp.2

/-- A square with an `O` marking does not contain an `X` marking. -/
theorem not_mem_XSet_of_mem_OSet {p : Fin n × Fin n} (hp : p ∈ G.OSet) : p ∉ G.XSet := by
  intro hpX
  exact G.not_mem_OSet_and_mem_XSet p ⟨hp, hpX⟩

/-- A square with an `X` marking does not contain an `O` marking. -/
theorem not_mem_OSet_of_mem_XSet {p : Fin n × Fin n} (hp : p ∈ G.XSet) : p ∉ G.OSet := by
  intro hpO
  exact G.not_mem_OSet_and_mem_XSet p ⟨hpO, hp⟩

/-- Relabel the rows of a grid diagram by relabeling both marking states. -/
def relabelRows (ρ : Equiv.Perm (Fin n)) (G : GridDiagram n) : GridDiagram n where
  O := G.O.relabelRows ρ
  X := G.X.relabelRows ρ
  disjoint := by
    intro c h
    exact G.disjoint c (ρ.injective h)

/-- Relabel the columns of a grid diagram by relabeling both marking states. -/
def relabelColumns (κ : Equiv.Perm (Fin n)) (G : GridDiagram n) : GridDiagram n where
  O := G.O.relabelColumns κ
  X := G.X.relabelColumns κ
  disjoint := by
    intro c h
    exact G.disjoint (κ.symm c) h

/-- The `O` marking state of a row-relabeled grid diagram. -/
@[simp]
theorem relabelRows_O (ρ : Equiv.Perm (Fin n)) : (G.relabelRows ρ).O = G.O.relabelRows ρ :=
  rfl

/-- The `X` marking state of a row-relabelled grid diagram. -/
@[simp]
theorem relabelRows_X (ρ : Equiv.Perm (Fin n)) : (G.relabelRows ρ).X = G.X.relabelRows ρ :=
  rfl

/-- The `O` marking state of a column-relabelled grid diagram. -/
@[simp]
theorem relabelColumns_O (κ : Equiv.Perm (Fin n)) : (G.relabelColumns κ).O = G.O.relabelColumns κ :=
  rfl

/-- The `X` marking state of a column-relabelled grid diagram. -/
@[simp]
theorem relabelColumns_X (κ : Equiv.Perm (Fin n)) : (G.relabelColumns κ).X = G.X.relabelColumns κ :=
  rfl

/-- Row relabeling evaluates on the `O` marking by applying the row permutation. -/
@[simp]
theorem relabelRows_O_apply (ρ : Equiv.Perm (Fin n)) (c : Fin n) :
    (G.relabelRows ρ).O c = ρ (G.O c) :=
  rfl

/-- Row relabeling evaluates on the `X` marking by applying the row permutation. -/
@[simp]
theorem relabelRows_X_apply (ρ : Equiv.Perm (Fin n)) (c : Fin n) :
    (G.relabelRows ρ).X c = ρ (G.X c) :=
  rfl

/-- Column relabeling evaluates on the `O` marking at the inverse old column. -/
@[simp]
theorem relabelColumns_O_apply (κ : Equiv.Perm (Fin n)) (c : Fin n) :
    (G.relabelColumns κ).O c = G.O (κ.symm c) :=
  rfl

/-- Column relabeling evaluates on the `X` marking at the inverse old column. -/
@[simp]
theorem relabelColumns_X_apply (κ : Equiv.Perm (Fin n)) (c : Fin n) :
    (G.relabelColumns κ).X c = G.X (κ.symm c) :=
  rfl

/-- Row relabeling transports the `O` marking set by the row permutation. -/
theorem mem_OSet_relabelRows (ρ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelRows ρ).OSet ↔ (p.1, ρ.symm p.2) ∈ G.OSet := by
  rw [OSet, OSet]
  exact GridState.mem_pointSet_relabelRows ρ G.O p

/-- Row relabeling transports the `X` marking set by the row permutation. -/
theorem mem_XSet_relabelRows (ρ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelRows ρ).XSet ↔ (p.1, ρ.symm p.2) ∈ G.XSet := by
  rw [XSet, XSet]
  exact GridState.mem_pointSet_relabelRows ρ G.X p

/-- Column relabeling transports the `O` marking set by the column permutation. -/
theorem mem_OSet_relabelColumns (κ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelColumns κ).OSet ↔ (κ.symm p.1, p.2) ∈ G.OSet := by
  simp [OSet]

/-- Column relabeling transports the `X` marking set by the column permutation. -/
theorem mem_XSet_relabelColumns (κ : Equiv.Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ (G.relabelColumns κ).XSet ↔ (κ.symm p.1, p.2) ∈ G.XSet := by
  simp [XSet]

/-- Swapping two rows in a grid diagram. -/
def swapRows (a b : Fin n) (G : GridDiagram n) : GridDiagram n :=
  G.relabelRows (Equiv.swap a b)

/-- Swapping two columns in a grid diagram. -/
def swapColumns (a b : Fin n) (G : GridDiagram n) : GridDiagram n :=
  G.relabelColumns (Equiv.swap a b)

/-- The `O` marking state of a row-swapped grid diagram. -/
@[simp]
theorem swapRows_O (a b : Fin n) : (G.swapRows a b).O = G.O.swapRows a b :=
  rfl

/-- The `X` marking state of a row-swapped grid diagram. -/
@[simp]
theorem swapRows_X (a b : Fin n) : (G.swapRows a b).X = G.X.swapRows a b :=
  rfl

/-- The `O` marking state of a column-swapped grid diagram. -/
@[simp]
theorem swapColumns_O (a b : Fin n) : (G.swapColumns a b).O = G.O.swapColumns a b :=
  rfl

/-- The `X` marking state of a column-swapped grid diagram. -/
@[simp]
theorem swapColumns_X (a b : Fin n) : (G.swapColumns a b).X = G.X.swapColumns a b :=
  rfl

/-- Row swaps transport the `O` marking set by the row transposition. -/
theorem mem_OSet_swapRows (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapRows a b).OSet ↔ (p.1, Equiv.swap a b p.2) ∈ G.OSet := by
  simpa [swapRows] using G.mem_OSet_relabelRows (Equiv.swap a b) p

/-- Row swaps transport the `X` marking set by the row transposition. -/
theorem mem_XSet_swapRows (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapRows a b).XSet ↔ (p.1, Equiv.swap a b p.2) ∈ G.XSet := by
  simpa [swapRows] using G.mem_XSet_relabelRows (Equiv.swap a b) p

/-- Column swaps transport the `O` marking set by the column transposition. -/
theorem mem_OSet_swapColumns (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapColumns a b).OSet ↔ (Equiv.swap a b p.1, p.2) ∈ G.OSet := by
  simp [swapColumns]

/-- Column swaps transport the `X` marking set by the column transposition. -/
theorem mem_XSet_swapColumns (a b : Fin n) (p : Fin n × Fin n) :
    p ∈ (G.swapColumns a b).XSet ↔ (Equiv.swap a b p.1, p.2) ∈ G.XSet := by
  simp [swapColumns]

/-- Swapping the same pair of rows twice is the identity on grid diagrams. -/
@[simp]
theorem swapRows_swapRows (a b : Fin n) : (G.swapRows a b).swapRows a b = G := by
  ext c <;> simp [swapRows]

/-- Swapping the same pair of columns twice is the identity on grid diagrams. -/
@[simp]
theorem swapColumns_swapColumns (a b : Fin n) : (G.swapColumns a b).swapColumns a b = G := by
  ext c <;> simp [swapColumns]

/-- Relabeling rows by the identity permutation does not change a grid diagram. -/
@[simp]
theorem relabelRows_refl : G.relabelRows (Equiv.refl (Fin n)) = G := by
  ext c <;> simp

/-- Relabeling columns by the identity permutation does not change a grid diagram. -/
@[simp]
theorem relabelColumns_refl : G.relabelColumns (Equiv.refl (Fin n)) = G := by
  ext c <;> simp

/-- Successive row relabelings compose on grid diagrams. -/
@[simp]
theorem relabelRows_relabelRows (ρ σ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).relabelRows σ = G.relabelRows (ρ.trans σ) := by
  ext c <;> simp

/-- Successive column relabelings compose on grid diagrams. -/
@[simp]
theorem relabelColumns_relabelColumns (κ τ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).relabelColumns τ = G.relabelColumns (κ.trans τ) := by
  ext c <;> simp

/-- Row and column relabeling commute on grid diagrams. -/
theorem relabelRows_relabelColumns (ρ κ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).relabelColumns κ = (G.relabelColumns κ).relabelRows ρ := by
  ext c <;> simp [GridState.relabelRows_relabelColumns]

/-- The diagonal reflection of a grid diagram, reflecting both the `O` and `X` marking states.

Reflection across the main diagonal is a bijection of squares, so it preserves the condition
that no square carries both markings. -/
def transpose (G : GridDiagram n) : GridDiagram n where
  O := G.O.transpose
  X := G.X.transpose
  disjoint := by
    intro c h
    simp only [GridState.transpose_apply] at h
    refine G.disjoint (G.O.toPerm.symm c) ?_
    rw [Equiv.apply_symm_apply, h, Equiv.apply_symm_apply]

/-- The `O` marking state of the reflected diagram is the reflected `O` marking state. -/
@[simp]
theorem transpose_O : G.transpose.O = G.O.transpose := rfl
/-- The `X` marking state of the reflected diagram is the reflected `X` marking state. -/
@[simp]
theorem transpose_X : G.transpose.X = G.X.transpose := rfl
/-- The reflected diagram's `O` row coordinate is the original `O` column in that row. -/
theorem transpose_O_apply (c : Fin n) : G.transpose.O c = OColumnOfRow G c := by simp [OColumnOfRow]
/-- The reflected diagram's `X` row coordinate is the original `X` column in that row. -/
theorem transpose_X_apply (c : Fin n) : G.transpose.X c = XColumnOfRow G c := by simp [XColumnOfRow]
/-- The `O` marking in row `c` of the reflected diagram lies in column `G.O c`. -/
@[simp]
theorem OColumnOfRow_transpose (c : Fin n) : OColumnOfRow G.transpose c = G.O c := by
  rw [OColumnOfRow, transpose_O]
  exact GridState.columnOfRow_transpose G.O c
/-- The `X` marking in row `c` of the reflected diagram lies in column `G.X c`. -/
@[simp]
theorem XColumnOfRow_transpose (c : Fin n) : XColumnOfRow G.transpose c = G.X c := by
  rw [XColumnOfRow, transpose_X]
  exact GridState.columnOfRow_transpose G.X c
/-- The diagonal reflection is an involution on grid diagrams. -/
@[simp]
theorem transpose_transpose : G.transpose.transpose = G := by ext c <;> simp
/-- Reflecting after a row relabeling is the same as column relabeling after reflecting. -/
@[simp]
theorem relabelRows_transpose (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).transpose = G.transpose.relabelColumns ρ := by
  ext c <;> simp

/-- Reflecting after a column relabeling is the same as row relabeling after reflecting. -/
@[simp]
theorem relabelColumns_transpose (κ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).transpose = G.transpose.relabelRows κ := by
  ext c <;> simp

/-- Reflecting after a row swap is the same as the corresponding column swap after reflecting. -/
@[simp]
theorem swapRows_transpose (a b : Fin n) :
    (G.swapRows a b).transpose = G.transpose.swapColumns a b := by
  simp [swapRows, swapColumns]

/-- Reflecting after a column swap is the same as the corresponding row swap after reflecting. -/
@[simp]
theorem swapColumns_transpose (a b : Fin n) :
    (G.swapColumns a b).transpose = G.transpose.swapRows a b := by
  simp [swapRows, swapColumns]

/-- The `O`-marking set of the reflected diagram is the diagonal reflection of the original
`O`-marking set. -/
theorem transpose_OSet : G.transpose.OSet = G.OSet.image Prod.swap := by
  rw [OSet, OSet, transpose_O, GridState.transpose_pointSet]

/-- The `X`-marking set of the reflected diagram is the diagonal reflection of the original
`X`-marking set. -/
theorem transpose_XSet : G.transpose.XSet = G.XSet.image Prod.swap := by
  rw [XSet, XSet, transpose_X, GridState.transpose_pointSet]

/-- A square lies in the reflected diagram's `O`-marking set exactly when its diagonal
reflection lies in the original `O`-marking set. -/
theorem mem_OSet_transpose (p : Fin n × Fin n) :
    p ∈ G.transpose.OSet ↔ Prod.swap p ∈ G.OSet := by
  rw [OSet, OSet, transpose_O]
  exact GridState.mem_pointSet_transpose G.O p

/-- A square lies in the reflected diagram's `X`-marking set exactly when its diagonal
reflection lies in the original `X`-marking set. -/
theorem mem_XSet_transpose (p : Fin n × Fin n) :
    p ∈ G.transpose.XSet ↔ Prod.swap p ∈ G.XSet := by
  rw [XSet, XSet, transpose_X]
  exact GridState.mem_pointSet_transpose G.X p

/-- The marking swap of a grid diagram, obtained by exchanging the `O`- and `X`-marking states.

The defining no-double-marking condition is symmetric in the two marking states, so the swap is
again a grid diagram. -/
def swapMarkings (G : GridDiagram n) : GridDiagram n where
  O := G.X
  X := G.O
  disjoint c := (G.disjoint c).symm

/-- The `O`-marking state of the marking swap is the original `X`-marking state. -/
@[simp]
theorem swapMarkings_O : G.swapMarkings.O = G.X := rfl

/-- The `X`-marking state of the marking swap is the original `O`-marking state. -/
@[simp]
theorem swapMarkings_X : G.swapMarkings.X = G.O := rfl

/-- Swapping markings changes the `O` row lookup to the original `X` row lookup. -/
@[simp]
theorem OColumnOfRow_swapMarkings (r : Fin n) :
    OColumnOfRow G.swapMarkings r = XColumnOfRow G r := rfl

/-- Swapping markings changes the `X` row lookup to the original `O` row lookup. -/
@[simp]
theorem XColumnOfRow_swapMarkings (r : Fin n) :
    XColumnOfRow G.swapMarkings r = OColumnOfRow G r := rfl

/-- The `O`-marking set of the marking swap is the original `X`-marking set. -/
@[simp]
theorem swapMarkings_OSet : G.swapMarkings.OSet = G.XSet := rfl

/-- The `X`-marking set of the marking swap is the original `O`-marking set. -/
@[simp]
theorem swapMarkings_XSet : G.swapMarkings.XSet = G.OSet := rfl

/-- Membership in the marking swap's `O`-marking set is membership in the original
`X`-marking set. -/
theorem mem_OSet_swapMarkings (p : Fin n × Fin n) :
    p ∈ G.swapMarkings.OSet ↔ p ∈ G.XSet := Iff.rfl

/-- Membership in the marking swap's `X`-marking set is membership in the original
`O`-marking set. -/
theorem mem_XSet_swapMarkings (p : Fin n × Fin n) :
    p ∈ G.swapMarkings.XSet ↔ p ∈ G.OSet := Iff.rfl

/-- The marking swap is an involution. -/
@[simp]
theorem swapMarkings_swapMarkings : G.swapMarkings.swapMarkings = G := by
  ext c <;> simp [swapMarkings]

/-- Row relabeling commutes with exchanging the two marking states. -/
@[simp]
theorem relabelRows_swapMarkings (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).swapMarkings = G.swapMarkings.relabelRows ρ := by
  ext c <;> simp [swapMarkings]

/-- Column relabeling commutes with exchanging the two marking states. -/
@[simp]
theorem relabelColumns_swapMarkings (κ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).swapMarkings = G.swapMarkings.relabelColumns κ := by
  ext c <;> simp [swapMarkings]

/-- Row swaps commute with exchanging the two marking states. -/
@[simp]
theorem swapRows_swapMarkings (a b : Fin n) :
    (G.swapRows a b).swapMarkings = G.swapMarkings.swapRows a b := by simp [swapRows]

/-- Column swaps commute with exchanging the two marking states. -/
@[simp]
theorem swapColumns_swapMarkings (a b : Fin n) :
    (G.swapColumns a b).swapMarkings = G.swapMarkings.swapColumns a b := by simp [swapColumns]

/-- The marking swap commutes with the diagonal reflection of a grid diagram. -/
@[simp]
theorem swapMarkings_transpose : G.swapMarkings.transpose = G.transpose.swapMarkings := by
  ext c <;> simp [swapMarkings]
end GridDiagram
end TauCeti
