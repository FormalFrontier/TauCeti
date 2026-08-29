/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.SideOverlap

/-!
# Cyclic order for overlapping empty grid rectangles

Two composable rectangles in a nondiagonal term of the grid differential square either have
disjoint side columns or share exactly one side column. In the latter case, constructing the
alternate two-rectangle decomposition requires knowing the cyclic order of the three side columns
and of the three rows at their corners.

This file proves the order constraint in the orientation where the common column is the initial
side of both rectangles. The two remaining side columns lie on opposite choices of the cyclic arc
from the common column. In either choice, emptiness forces the common corner row to lie strictly
between the other two rows. Thus the two rectangles form one of the two L-shaped configurations
that can be recut along the other internal edge.

The proof uses emptiness for both the source and target state of a rectangle. If the third column
lies in the first rectangle's column interior, its state point must miss that rectangle's row
interior; if it lies in the second rectangle's column interior, the corresponding point must miss
the second row interior. Circular-order trichotomy turns either exclusion into the same cyclic row
order.

## Main results

* `TauCeti.GridRectangleDecomposition.side_eq_cases_of_hasOneCommonSide`: the four possible
  orientations of the unique common side, with the two other sides distinct.
* `TauCeti.GridRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left`: when the common
  side is the initial side of both empty rectangles, their other side columns determine one of
  two cyclic orders and the shared corner row lies between the other two rows.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and
`∂² = 0`", specifically the overlapping case in the juxtaposition proof. The cyclic-order
argument follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

private theorem mem_cIoo_cyclic_left {a b c : Fin n} (h : b ∈ Grid.cIoo a c) :
    c ∈ Grid.cIoo b a := by
  rw [Grid.mem_cIoo] at h ⊢
  constructor
  · intro hba
    subst b
    split_ifs at h <;> omega
  · split_ifs at h ⊢ <;> omega

private theorem mem_cIoo_cyclic_right {a b c : Fin n} (h : b ∈ Grid.cIoo a c) :
    a ∈ Grid.cIoo c b := by
  exact mem_cIoo_cyclic_left (mem_cIoo_cyclic_left h)

private theorem mem_cIoo_swap_of_not_mem {a b c : Fin n} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (h : c ∉ Grid.cIoo a b) : c ∈ Grid.cIoo b a := by
  rcases (Grid.not_mem_cIoo_iff hab).mp h with hca' | hcb' | hswap
  · exact (hca hca').elim
  · exact (hcb hcb').elim
  · exact hswap

/-- Suppose the two empty rectangles in a decomposition share their initial side column and no
other side. Then their two terminal sides occur in one of the two possible cyclic orders around
the common side, while the row of the common corner lies strictly between the other two corner
rows.

The disjunction records which L-shaped repartition is needed later. The row order is independent
of that choice: emptiness of the rectangle whose column interval contains the third side forces
the corresponding third corner outside its row interior. -/
theorem cyclicOrder_of_isEmpty_of_left_eq_left (D : GridRectangleDecomposition x z)
    (hleft : D.first.left = D.second.left) (hright : D.first.right ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    (D.first.right ∈ Grid.cIoo D.first.left D.second.right ∨
        D.second.right ∈ Grid.cIoo D.first.left D.first.right) ∧
      D.first.top ∈ Grid.cIoo D.first.bottom D.second.top := by
  have hsecondRight_ne_firstLeft : D.second.right ≠ D.first.left :=
    fun h => D.second.left_ne_right (hleft.symm.trans h.symm)
  have hbottom : D.second.bottom = D.first.top := by
    rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, ← hleft]
    exact D.first.map_left
  have htop_ne_firstBottom : D.second.top ≠ D.first.bottom := by
    intro h
    apply hright
    apply D.middle.toPerm.injective
    rw [← GridRectangleBetween.top_def, h, D.first.map_right]
    exact D.first.bottom_def.symm
  have htop_ne_firstTop : D.second.top ≠ D.first.top := by
    rw [← hbottom]
    exact D.second.bottom_ne_top.symm
  have hcolumns :
      D.first.right ∈ Grid.cIoo D.first.left D.second.right ∨
        D.first.right ∈ Grid.cIoo D.second.right D.first.left :=
    (Grid.mem_cIoo_or_mem_cIoo_swap_iff hsecondRight_ne_firstLeft.symm).mpr
      ⟨D.first.left_ne_right.symm, hright⟩
  rcases hcolumns with hfirstRight | hfirstRight
  · have hnot : D.first.bottom ∉ Grid.cIoo D.first.top D.second.top := by
      intro hrow
      exact D.second.not_mem_interior_of_isEmpty hsecond
        D.first.right_bottom_mem_target
        (by
          rw [GridRectangle.mem_interior]
          constructor
          · simpa only [GridRectangle.mem_columnInterior,
              GridRectangleBetween.toGridRectangle_left,
              GridRectangleBetween.toGridRectangle_right, ← hleft] using hfirstRight
          · simpa only [GridRectangle.mem_rowInterior,
              GridRectangleBetween.toGridRectangle_bottom,
              GridRectangleBetween.toGridRectangle_top, hbottom] using hrow)
    have hrow := mem_cIoo_swap_of_not_mem D.second.bottom_ne_top
      (by simpa only [hbottom] using D.first.bottom_ne_top)
      (by simpa only [hbottom] using htop_ne_firstBottom.symm) (by simpa only [hbottom] using hnot)
    exact ⟨Or.inl hfirstRight, by
      simpa only [hbottom] using mem_cIoo_cyclic_left hrow⟩
  · have hsecondRight : D.second.right ∈ Grid.cIoo D.first.left D.first.right :=
      mem_cIoo_cyclic_right hfirstRight
    have hnot : D.second.top ∉ Grid.cIoo D.first.bottom D.first.top := by
      intro hrow
      exact D.first.not_mem_interior_target_of_isEmpty hfirst
        D.second.right_top_mem_source
        (by
          rw [GridRectangle.mem_interior]
          constructor
          · simpa only [GridRectangle.mem_columnInterior,
              GridRectangleBetween.toGridRectangle_left,
              GridRectangleBetween.toGridRectangle_right] using hsecondRight
          · simpa only [GridRectangle.mem_rowInterior,
              GridRectangleBetween.toGridRectangle_bottom,
              GridRectangleBetween.toGridRectangle_top] using hrow)
    have hrow := mem_cIoo_swap_of_not_mem D.first.bottom_ne_top
      htop_ne_firstBottom htop_ne_firstTop hnot
    exact ⟨Or.inr hsecondRight, mem_cIoo_cyclic_right hrow⟩

end GridRectangleDecomposition

end TauCeti
