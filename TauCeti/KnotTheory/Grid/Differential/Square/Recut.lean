/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.OverlapOrder
public import TauCeti.KnotTheory.Grid.Rectangle.Juxtaposition
public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# Recutting a two-step grid rectangle decomposition along its other internal edge

A nondiagonal term in the square of the unblocked grid differential `∂⁻` is a pair of composable
empty rectangles whose two pairs of side columns are either disjoint or share exactly one column.
In the second case the two rectangles meet at a corner and their union is an L-shaped hexagon,
which can be cut into two rectangles in exactly one other way. This file builds that alternate cut
in the orientation where the two rectangles share their *initial* side column, and shows that it
is again a decomposition by two rectangles the unblocked differential counts, carrying the same
weight and passing through a different intermediate grid state.

The relation between the two cuts is packaged as `GridRectangleDecomposition.IsRecut`: the
rectangles of each cut cover disjoint sets of squares, and the two unions agree. That is exactly
the amount of information a weight needs: any multiplicative function of squares has the same
product on the two cuts, and in particular the `O`-monomials multiply to the same polynomial and
`X`-avoidance transfers.

The geometric input is the cyclic order forced by emptiness
(`cyclicOrder_of_isEmpty_of_left_eq_left`) and the finite-domain repartition identity for the
covered squares (`GridRectangle.coveredSquares_union_eq_of_mem_cIoo` and its complementary form).
Emptiness of the new rectangles is not part of that identity: it is proved here, and it is where
emptiness of *both* old rectangles is used, one for the columns below the cut and one for the
columns above it.

Three orientations of the shared side column remain: the two rectangles may share their terminal
side, or the terminal side of one may be the initial side of the other. Those three, and the
assembly of the disjoint, overlapping and annular cases into `∂⁻ ∘ ∂⁻ = 0`, are separate steps.

## Main definitions

* `TauCeti.GridRectangleDecomposition.IsRecut`: two two-step decompositions with the same
  endpoints partition the same set of covered squares, through different intermediate states.

## Main results

* `TauCeti.GridRectangleDecomposition.IsRecut.prod_coveredSquares_mul_prod_coveredSquares`: a
  recut preserves the product of any multiplicative weight on squares.
* `TauCeti.GridRectangleDecomposition.IsRecut.OMonomial_mul_OMonomial`: a recut preserves the
  product of the `O`-monomial weights of the unblocked differential.
* `TauCeti.GridRectangleDecomposition.IsRecut.disjoint_XSet_first`,
  `TauCeti.GridRectangleDecomposition.IsRecut.disjoint_XSet_second`: `X`-avoidance transfers
  across a recut.
* `TauCeti.GridRectangleDecomposition.exists_isRecut_of_left_eq_left`: two composable empty
  rectangles sharing their initial side column admit a recut by two empty rectangles.
* `TauCeti.GridRectangleDecomposition.exists_unblockedRectangles_recut_of_left_eq_left`: the
  resulting pairing of the terms of `∂⁻ ∘ ∂⁻`, with equal weights and distinct intermediate
  states.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and
`∂² = 0`", specifically the overlapping case of its juxtaposition case analysis. The recut follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-! ### Two cuts of the same two-step domain -/

/-- `E` is a *recut* of the two-step decomposition `D`: the two decompositions have the same
endpoints, each cuts its domain into two rectangles covering disjoint sets of squares, the two
domains agree, and the two cuts pass through different intermediate grid states.

This is the pairing relation used by the juxtaposition proof of `∂⁻ ∘ ∂⁻ = 0`: the terms of the
differential square indexed by `D` and by `E` carry the same weight and cancel in characteristic
two. -/
structure IsRecut (D E : GridRectangleDecomposition x z) : Prop where
  /-- The two cuts pass through different intermediate grid states. -/
  middle_ne : E.middle ≠ D.middle
  /-- The two rectangles of `D` cover disjoint sets of squares. -/
  disjoint_coveredSquares :
    Disjoint D.first.toGridRectangle.coveredSquares D.second.toGridRectangle.coveredSquares
  /-- The two rectangles of `E` cover disjoint sets of squares. -/
  disjoint_coveredSquares_recut :
    Disjoint E.first.toGridRectangle.coveredSquares E.second.toGridRectangle.coveredSquares
  /-- The two cuts cover the same squares. -/
  coveredSquares_union_eq :
    E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares =
      D.first.toGridRectangle.coveredSquares ∪ D.second.toGridRectangle.coveredSquares

namespace IsRecut

variable {D E : GridRectangleDecomposition x z}

/-- Being a recut is a symmetric relation. -/
theorem symm (h : D.IsRecut E) : E.IsRecut D where
  middle_ne := h.middle_ne.symm
  disjoint_coveredSquares := h.disjoint_coveredSquares_recut
  disjoint_coveredSquares_recut := h.disjoint_coveredSquares
  coveredSquares_union_eq := h.coveredSquares_union_eq.symm

/-- A recut preserves the product of any multiplicative weight on squares: both cuts partition
the same finite set of covered squares. -/
theorem prod_coveredSquares_mul_prod_coveredSquares (h : D.IsRecut E) {M : Type*} [CommMonoid M]
    (f : Fin n × Fin n → M) :
    (∏ p ∈ E.first.toGridRectangle.coveredSquares, f p) *
        ∏ p ∈ E.second.toGridRectangle.coveredSquares, f p =
      (∏ p ∈ D.first.toGridRectangle.coveredSquares, f p) *
        ∏ p ∈ D.second.toGridRectangle.coveredSquares, f p := by
  rw [← Finset.prod_union h.disjoint_coveredSquares_recut, h.coveredSquares_union_eq,
    Finset.prod_union h.disjoint_coveredSquares]

/-- A recut preserves the product of the `O`-monomial weights that the unblocked differential
attaches to its two rectangles. -/
theorem OMonomial_mul_OMonomial (h : D.IsRecut E) (G : GridDiagram n) (R : Type*)
    [CommSemiring R] :
    G.OMonomial R E.first.toGridRectangle * G.OMonomial R E.second.toGridRectangle =
      G.OMonomial R D.first.toGridRectangle * G.OMonomial R D.second.toGridRectangle := by
  simp only [G.OMonomial_eq_prod_coveredSquares R]
  exact h.prod_coveredSquares_mul_prod_coveredSquares _

/-- If neither rectangle of `D` covers an `X`-marking, then neither does the first rectangle of a
recut of `D`. -/
theorem disjoint_XSet_first (h : D.IsRecut E) {G : GridDiagram n}
    (h₁ : Disjoint D.first.toGridRectangle.coveredSquares G.XSet)
    (h₂ : Disjoint D.second.toGridRectangle.coveredSquares G.XSet) :
    Disjoint E.first.toGridRectangle.coveredSquares G.XSet := by
  have hunion : Disjoint
      (E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares)
      G.XSet := by
    rw [h.coveredSquares_union_eq]
    exact Finset.disjoint_union_left.mpr ⟨h₁, h₂⟩
  exact (Finset.disjoint_union_left.mp hunion).1

/-- If neither rectangle of `D` covers an `X`-marking, then neither does the second rectangle of a
recut of `D`. -/
theorem disjoint_XSet_second (h : D.IsRecut E) {G : GridDiagram n}
    (h₁ : Disjoint D.first.toGridRectangle.coveredSquares G.XSet)
    (h₂ : Disjoint D.second.toGridRectangle.coveredSquares G.XSet) :
    Disjoint E.second.toGridRectangle.coveredSquares G.XSet := by
  have hunion : Disjoint
      (E.first.toGridRectangle.coveredSquares ∪ E.second.toGridRectangle.coveredSquares)
      G.XSet := by
    rw [h.coveredSquares_union_eq]
    exact Finset.disjoint_union_left.mpr ⟨h₁, h₂⟩
  exact (Finset.disjoint_union_left.mp hunion).2

end IsRecut

/-! ### Building the recut -/

/-- The recut in the configuration where the terminal side of the first rectangle lies strictly
inside the column span of the second one.

The two rectangles `{a, b} × {x a, x b}` and `{a, d} × {x b, x d}` are cut apart along the column
line `b` instead of the row line `x b`. -/
private theorem exists_recut_columnCut {a b d : Fin n}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hz : z = (x.swapColumns a b).swapColumns a d)
    (hcol : b ∈ Grid.cIoo a d) (hrow : x b ∈ Grid.cIoo (x a) (x d))
    (hfirst : ∀ c ∈ Grid.cIoo a b, x c ∉ Grid.cIoo (x a) (x b))
    (hsecond : ∀ c ∈ Grid.cIoo a d, c ≠ a → c ≠ b → x c ∉ Grid.cIoo (x b) (x d)) :
    ∃ E : GridRectangleDecomposition x z,
      E.middle = x.swapColumns b d ∧
        E.first.toGridRectangle = { left := b, right := d, bottom := x b, top := x d } ∧
          E.second.toGridRectangle = { left := a, right := b, bottom := x a, top := x d } ∧
            E.first.IsEmpty ∧ E.second.IsEmpty := by
  have hz' : z = (x.swapColumns b d).swapColumns a b := by
    rw [hz, GridState.swapColumns_swapColumns_conj x b d a b, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
  have hmid_a : (x.swapColumns b d) a = x a := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hab had]
  have hmid_b : (x.swapColumns b d) b = x d := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_left]
  refine ⟨{ middle := x.swapColumns b d
            first := GridRectangleBetween.ofSwapColumns x _ b d hbd rfl
            second := GridRectangleBetween.ofSwapColumns _ z a b hab hz' }, rfl, by simp,
          by simp [hmid_a, hmid_b], ?_, ?_⟩
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top]
    intro c hc
    have hcad : c ∈ Grid.cIoo a d := Grid.cIoo_subset_cIoo_of_mem_cIoo_right hcol hc
    have hca : c ≠ a := by
      rintro rfl
      exact Grid.left_notMem_cIoo _ _ hcad
    have hcb : c ≠ b := by
      rintro rfl
      exact Grid.left_notMem_cIoo _ _ hc
    exact hsecond c hcad hca hcb
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top, hmid_a,
      hmid_b]
    intro c hc hmem
    have hca : c ≠ a := by
      rintro rfl
      exact Grid.left_notMem_cIoo _ _ hc
    have hcb : c ≠ b := by
      rintro rfl
      exact Grid.right_notMem_cIoo _ _ hc
    have hcad : c ∈ Grid.cIoo a d := Grid.cIoo_subset_cIoo_of_mem_cIoo_left hcol hc
    have hcd : c ≠ d := by
      rintro rfl
      exact Grid.right_notMem_cIoo _ _ hcad
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcb hcd] at hmem
    have hcut : x c ∈ Grid.cIoo (x a) (x b) ∪ insert (x b) (Grid.cIoo (x b) (x d)) := by
      rw [Grid.cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo hrow]
      exact hmem
    rw [Finset.mem_union, Finset.mem_insert] at hcut
    rcases hcut with hcut | hcut | hcut
    · exact hfirst c hc hcut
    · exact hcb (x.toPerm.injective hcut)
    · exact hsecond c hcad hca hcb hcut

/-- The recut in the configuration where the terminal side of the second rectangle lies strictly
inside the column span of the first one.

The two rectangles `{a, b} × {x a, x b}` and `{a, d} × {x b, x d}` are cut apart along the column
line `d` instead of the row line `x b`. -/
private theorem exists_recut_complementaryColumnCut {a b d : Fin n}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hz : z = (x.swapColumns a b).swapColumns a d)
    (hcol : d ∈ Grid.cIoo a b) (hrow : x b ∈ Grid.cIoo (x a) (x d))
    (hfirst : ∀ c ∈ Grid.cIoo a b, x c ∉ Grid.cIoo (x a) (x b))
    (hsecond : ∀ c ∈ Grid.cIoo a d, c ≠ a → c ≠ b → x c ∉ Grid.cIoo (x b) (x d)) :
    ∃ E : GridRectangleDecomposition x z,
      E.middle = x.swapColumns a d ∧
        E.first.toGridRectangle = { left := a, right := d, bottom := x a, top := x d } ∧
          E.second.toGridRectangle = { left := d, right := b, bottom := x a, top := x b } ∧
            E.first.IsEmpty ∧ E.second.IsEmpty := by
  have hz' : z = (x.swapColumns a d).swapColumns d b := by
    rw [hz, GridState.swapColumns_swapColumns_conj x a b a d, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hab.symm hbd]
  have hmid_d : (x.swapColumns a d) d = x a := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_right]
  have hmid_b : (x.swapColumns a d) b = x b := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hab.symm hbd]
  refine ⟨{ middle := x.swapColumns a d
            first := GridRectangleBetween.ofSwapColumns x _ a d had rfl
            second := GridRectangleBetween.ofSwapColumns _ z d b hbd.symm hz' }, rfl, by simp,
          by simp [hmid_d, hmid_b], ?_, ?_⟩
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top]
    intro c hc hmem
    have hca : c ≠ a := by
      rintro rfl
      exact Grid.left_notMem_cIoo _ _ hc
    have hcd : c ≠ d := by
      rintro rfl
      exact Grid.right_notMem_cIoo _ _ hc
    have hcab : c ∈ Grid.cIoo a b := Grid.cIoo_subset_cIoo_of_mem_cIoo_left hcol hc
    have hcb : c ≠ b := by
      rintro rfl
      exact Grid.right_notMem_cIoo _ _ hcab
    have hcut : x c ∈ Grid.cIoo (x a) (x b) ∪ insert (x b) (Grid.cIoo (x b) (x d)) := by
      rw [Grid.cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo hrow]
      exact hmem
    rw [Finset.mem_union, Finset.mem_insert] at hcut
    rcases hcut with hcut | hcut | hcut
    · exact hfirst c hcab hcut
    · exact hcb (x.toPerm.injective hcut)
    · exact hsecond c hc hca hcb hcut
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top, hmid_d,
      hmid_b]
    intro c hc
    have hcab : c ∈ Grid.cIoo a b := Grid.cIoo_subset_cIoo_of_mem_cIoo_right hcol hc
    have hca : c ≠ a := by
      rintro rfl
      exact Grid.left_notMem_cIoo _ _ hcab
    have hcd : c ≠ d := by
      rintro rfl
      exact Grid.left_notMem_cIoo _ _ hc
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hca hcd]
    exact hfirst c hcab

/-! ### The recut of a decomposition sharing its initial side column -/

/-- Two composable empty rectangles that share their initial side column and no other side admit
a *recut*: the L-shaped union of their domains has a second decomposition into two empty
rectangles, through a different intermediate grid state.

Emptiness of both rectangles enters twice. It fixes the cyclic order of the three side columns
and of the three corner rows, and it then transfers to the two new rectangles: the part of a new
rectangle below the cut is controlled by the first old rectangle and the part above it by the
second. -/
theorem exists_isRecut_of_left_eq_left (D : GridRectangleDecomposition x z)
    (hleft : D.first.left = D.second.left) (hright : D.first.right ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    ∃ E : GridRectangleDecomposition x z, D.IsRecut E ∧ E.first.IsEmpty ∧ E.second.IsEmpty := by
  have hab : D.first.left ≠ D.first.right := D.first.left_ne_right
  have had : D.first.left ≠ D.second.right := by
    rw [hleft]
    exact D.second.left_ne_right
  have hmid : D.middle = x.swapColumns D.first.left D.first.right :=
    D.first.target_eq_swapColumns
  have hmid_first : D.middle D.first.left = x D.first.right := D.first.map_left
  have hmid_second : D.middle D.second.right = x D.second.right :=
    D.first.map_of_ne _ had.symm hright.symm
  have hz : z = (x.swapColumns D.first.left D.first.right).swapColumns D.first.left
      D.second.right := by
    rw [← hmid, hleft]
    exact D.second.target_eq_swapColumns
  obtain ⟨hcolcase, hrow⟩ := D.cyclicOrder_of_isEmpty_of_left_eq_left hleft hright hfirst hsecond
  simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hmid_second] at hrow
  have hfirst' : ∀ c ∈ Grid.cIoo D.first.left D.first.right,
      x c ∉ Grid.cIoo (x D.first.left) (x D.first.right) := by
    have h := hfirst
    rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo] at h
    simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def] using h
  have hsecond' : ∀ c ∈ Grid.cIoo D.first.left D.second.right, c ≠ D.first.left →
      c ≠ D.first.right → x c ∉ Grid.cIoo (x D.first.right) (x D.second.right) := by
    have h := hsecond
    rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo] at h
    simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, ← hleft, hmid_first,
      hmid_second] at h
    intro c hc hca hcb
    have hcm := h c hc
    rwa [D.first.map_of_ne c hca hcb] at hcm
  have hD1 : D.first.toGridRectangle =
      { left := D.first.left, right := D.first.right, bottom := x D.first.left,
        top := x D.first.right } := rfl
  have hD2 : D.second.toGridRectangle =
      { left := D.first.left, right := D.second.right, bottom := x D.first.right,
        top := x D.second.right } := by
    have hlit : D.second.toGridRectangle =
        { left := D.second.left, right := D.second.right, bottom := D.second.bottom,
          top := D.second.top } := rfl
    have hb2 : D.second.bottom = x D.first.right := by
      rw [GridRectangleBetween.bottom_def, ← hleft]
      exact hmid_first
    have ht2 : D.second.top = x D.second.right := by
      rw [GridRectangleBetween.top_def]
      exact hmid_second
    rw [hlit, hb2, ht2, ← hleft]
  have hDdisj : Disjoint D.first.toGridRectangle.coveredSquares
      D.second.toGridRectangle.coveredSquares := by
    rw [hD1, hD2]
    exact (GridRectangle.disjoint_coveredSquares_iff _ _).mpr (Or.inr (by
      simpa only [GridRectangle.coveredRows_def] using
        Grid.disjoint_cIco_cIco_of_mem_cIoo hrow))
  rcases hcolcase with hcol | hcol
  · obtain ⟨E, hmidE, hE1, hE2, hEfirst, hEsecond⟩ :=
      exists_recut_columnCut hab had hright hz hcol hrow hfirst' hsecond'
    refine ⟨E, ⟨?_, hDdisj, ?_, ?_⟩, hEfirst, hEsecond⟩
    · intro h
      have hval : E.middle D.first.left = D.middle D.first.left := by rw [h]
      rw [hmidE, hmid_first] at hval
      simp only [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hab had] at hval
      exact hab (x.toPerm.injective hval)
    · rw [hE1, hE2]
      exact (GridRectangle.disjoint_coveredSquares_iff _ _).mpr (Or.inl (by
        simpa only [GridRectangle.coveredColumns_def] using
          (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol).symm))
    · rw [hE1, hE2, hD1, hD2]
      exact (GridRectangle.coveredSquares_union_eq_of_mem_cIoo hcol hrow).symm
  · obtain ⟨E, hmidE, hE1, hE2, hEfirst, hEsecond⟩ :=
      exists_recut_complementaryColumnCut hab had hright hz hcol hrow hfirst' hsecond'
    refine ⟨E, ⟨?_, hDdisj, ?_, ?_⟩, hEfirst, hEsecond⟩
    · intro h
      have hval : E.middle D.first.right = D.middle D.first.right := by rw [h]
      rw [hmidE, D.first.map_right] at hval
      simp only [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hab.symm hright] at hval
      exact hab (x.toPerm.injective hval).symm
    · rw [hE1, hE2]
      exact (GridRectangle.disjoint_coveredSquares_iff _ _).mpr (Or.inl (by
        simpa only [GridRectangle.coveredColumns_def] using
          Grid.disjoint_cIco_cIco_of_mem_cIoo hcol))
    · rw [hE1, hE2, hD1, hD2]
      exact (GridRectangle.coveredSquares_union_eq_of_mem_cIoo_complementary_col_cut hcol
        hrow).symm

/-- The pairing of two-step terms of `∂⁻ ∘ ∂⁻` in the orientation where the two rectangles share
their initial side column.

A pair of composable rectangles that the unblocked differential counts is matched with a second
such pair, through a different intermediate grid state and with the same product of weights. Over
a coefficient ring of characteristic two the two terms therefore cancel. -/
theorem exists_unblockedRectangles_recut_of_left_eq_left (G : GridDiagram n) (R : Type*)
    [CommSemiring R] (D : GridRectangleDecomposition x z)
    (hleft : D.first.left = D.second.left) (hright : D.first.right ≠ D.second.right)
    (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    ∃ E : GridRectangleDecomposition x z,
      E.middle ≠ D.middle ∧ E.first ∈ G.unblockedRectangles x E.middle ∧
        E.second ∈ G.unblockedRectangles E.middle z ∧
          G.OMonomial R E.first.toGridRectangle * G.OMonomial R E.second.toGridRectangle =
            G.OMonomial R D.first.toGridRectangle * G.OMonomial R D.second.toGridRectangle := by
  obtain ⟨E, hrecut, hEfirst, hEsecond⟩ := D.exists_isRecut_of_left_eq_left hleft hright
    (G.isEmpty_of_mem_unblockedRectangles hfirst) (G.isEmpty_of_mem_unblockedRectangles hsecond)
  have hX₁ := G.disjoint_XSet_of_mem_unblockedRectangles hfirst
  have hX₂ := G.disjoint_XSet_of_mem_unblockedRectangles hsecond
  exact ⟨E, hrecut.middle_ne,
    (G.mem_unblockedRectangles _).mpr ⟨hEfirst, hrecut.disjoint_XSet_first hX₁ hX₂⟩,
    (G.mem_unblockedRectangles _).mpr ⟨hEsecond, hrecut.disjoint_XSet_second hX₁ hX₂⟩,
    hrecut.OMonomial_mul_OMonomial G R⟩

end GridRectangleDecomposition

end TauCeti
