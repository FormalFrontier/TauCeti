/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.KnotTheory.Grid.Unknot
import TauCeti.GroupTheory.Perm.CyclePower

/-!
# The standard torus link grid diagrams

This file builds the standard grid diagram of the `(p + 1, q + 1)` torus link: on a grid of size
`(p + 1) + (q + 1)` the `O` markings sit on the diagonal and the `X` markings sit on the diagonal
shifted up by `q + 1` rows. Following the markings alternately horizontally and vertically shifts
the column down by `q + 1` each time, so the component permutation is the inverse of the
`(q + 1)`-st power of the cyclic shift `finRotate`. The smallest members are the standard unknot
grids (`q = 0`), the `4 × 4` grid with `p = q = 1`, and the `5 × 5` grid with `p = 1`, `q = 2`.

The cycle decomposition of the component permutation is computed from
`TauCeti.cycleType_pow_of_isCycle`: the diagram has exactly `gcd (p + 1) (q + 1)` link components,
all of them carrying the same number `((p + 1) + (q + 1)) / gcd (p + 1) (q + 1)` of markings, and
it represents a knot exactly when `p + 1` and `q + 1` are coprime. That is all that is proved
here.

Everything else in the name "torus link" is informal motivation and is *not* established by this
file: that the staircase traversal is the closure of the `(p + 1)`-strand braid winding `q + 1`
times around, hence the `(p + 1, q + 1)` torus link — of which the classical component count is
indeed `gcd (p + 1) (q + 1)`, matching the count proved here — and, in the same vein, the
readings of the members above as the unknot, the Hopf link, and the trefoil. As the roadmap's
standing convention has it, a link *is* a grid diagram modulo grid moves at this stage, and the
comparison with other presentations of a link belongs to the separate reconciliation lane; until
that lane runs, the classical names are labels for these diagrams, not theorems about them.

## Main definitions

* `TauCeti.GridDiagram.torusLink`: the standard grid diagram of the `(p + 1, q + 1)` torus link,
  of grid number `(p + 1) + (q + 1)`.

## Main results

* `TauCeti.GridDiagram.torusLink_zero_right`: with `q = 0` this is the standard unknot grid.
* `TauCeti.GridDiagram.componentPerm_torusLink`: the component permutation is the inverse of the
  `(q + 1)`-st power of the cyclic shift.
* `TauCeti.GridDiagram.componentCycleType_torusLink` and
  `TauCeti.GridDiagram.componentCount_torusLink`: there are `gcd (p + 1) (q + 1)` components, of
  equal size.
* `TauCeti.GridDiagram.isKnot_torusLink_iff`: the diagram represents a knot exactly when `p + 1`
  and `q + 1` are coprime.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.1, "Grid diagrams and
grid states", and supplies the family of diagrams that Lane G.7 needs for `τ(T_{p,q})` and the
Milnor conjecture, together with the `5 × 5` trefoil grid named in the acceptance criteria. The
diagram follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

variable (p q : ℕ)

/-! ### The cyclic shift of a torus link grid -/

/-- The cyclic shift of the columns of a torus link grid is a cycle. -/
private theorem isCycle_finRotate_torus : (finRotate (p + 1 + (q + 1))).IsCycle :=
  isCycle_finRotate_of_le (by omega)

/-- The cyclic shift of the columns of a torus link grid moves every column. -/
private theorem support_finRotate_torus :
    (finRotate (p + 1 + (q + 1))).support = Finset.univ :=
  support_finRotate_of_le (by omega)

/-- The cyclic shift of the columns of a torus link grid is a cycle of length the grid number. -/
private theorem card_support_finRotate_torus :
    (finRotate (p + 1 + (q + 1))).support.card = p + 1 + (q + 1) := by
  rw [support_finRotate_torus, Finset.card_univ, Fintype.card_fin]

/-- The shift `q + 1` of the `X` markings of a torus link grid is not a multiple of the grid
number, which is what makes the shifted diagonal disjoint from the diagonal. -/
private theorem not_card_dvd_torus :
    ¬(finRotate (p + 1 + (q + 1))).support.card ∣ q + 1 := by
  rw [card_support_finRotate_torus]
  exact Nat.not_dvd_of_pos_of_lt q.succ_pos (by omega)

/-! ### The diagram -/

/-- The standard grid diagram of the `(p + 1, q + 1)` torus link, of grid number
`(p + 1) + (q + 1)`.

The `O` markings occupy the diagonal squares and the `X` markings the diagonal shifted up by
`q + 1` rows. Following the markings alternately horizontally and vertically traverses staircases
that wind `q + 1` times around the torus in one direction and `p + 1` times in the other. -/
def torusLink : GridDiagram (p + 1 + (q + 1)) where
  O := ⟨1⟩
  X := ⟨finRotate (p + 1 + (q + 1)) ^ (q + 1)⟩
  disjoint := by
    intro c h
    exact pow_apply_ne_self_of_isCycle (isCycle_finRotate_torus p q) (not_card_dvd_torus p q)
      (by rw [support_finRotate_torus]; exact Finset.mem_univ c) (by simpa using h.symm)

-- The body of `torusLink` is deliberately not exposed, so the projection lemmas below are
-- written `(rfl)` rather than `rfl`: the parentheses opt out of exporting the definitional
-- equality, which downstream modules do not need and which the lemmas themselves replace.

/-- The `O` markings of a standard torus link grid are the identity permutation graph. -/
@[simp]
theorem torusLink_O_toPerm : (torusLink p q).O.toPerm = 1 :=
  (rfl)

/-- The `X` markings of a standard torus link grid are the `(q + 1)`-st power of the cyclic shift
permutation graph. -/
@[simp]
theorem torusLink_X_toPerm :
    (torusLink p q).X.toPerm = finRotate (p + 1 + (q + 1)) ^ (q + 1) :=
  (rfl)

-- Not `@[simp]`: the `simp` normal form of `(torusLink p q).O c` goes through the marking-state
-- lemma `torusLink_O_toPerm` above, which already rewrites it to `c`, so tagging the pointwise
-- form is a `simpNF` violation ("simp can prove this"). The same holds for the `X` marking.
/-- The `O` marking of a standard torus link grid in a column is in the diagonal row. -/
theorem torusLink_O_apply (c : Fin (p + 1 + (q + 1))) : (torusLink p q).O c = c :=
  (rfl)

/-- The `X` marking of a standard torus link grid in a column is `q + 1` rows above the
diagonal. -/
theorem torusLink_X_apply (c : Fin (p + 1 + (q + 1))) :
    (torusLink p q).X c = (finRotate (p + 1 + (q + 1)) ^ (q + 1)) c :=
  (rfl)

/-- With `q = 0` the standard torus link grid is the standard unknot grid: the `(p + 1, 1)` torus
link is the unknot. -/
theorem torusLink_zero_right : torusLink p 0 = unknot p := by
  refine GridDiagram.ext (GridState.ext fun c => ?_) (GridState.ext fun c => ?_)
  · rw [torusLink_O_apply, unknot_O_apply]
  · rw [torusLink_X_apply, unknot_X_apply, pow_one]

/-- A standard torus link grid is invariant under shifting all rows and all columns by one at the
same time: the shift commutes with its own power. -/
theorem relabelRows_relabelColumns_torusLink :
    ((torusLink p q).relabelRows (finRotate (p + 1 + (q + 1)))).relabelColumns
        (finRotate (p + 1 + (q + 1))) = torusLink p q := by
  have hcomm : Commute (finRotate (p + 1 + (q + 1))) (finRotate (p + 1 + (q + 1)) ^ (q + 1)) :=
    Commute.self_pow _ (q + 1)
  refine GridDiagram.ext (GridState.ext fun c => ?_) (GridState.ext fun c => ?_)
  · rw [relabelColumns_O_apply, relabelRows_O_apply, torusLink_O_apply, torusLink_O_apply,
      Equiv.apply_symm_apply]
  · rw [relabelColumns_X_apply, relabelRows_X_apply, torusLink_X_apply, torusLink_X_apply,
      ← Equiv.Perm.mul_apply, hcomm.eq, Equiv.Perm.mul_apply, Equiv.apply_symm_apply]

/-! ### The represented link and its components -/

/-- Traversing a standard torus link grid from an `O` marking to the `X` marking in its row and
back down to the next `O` marking shifts the column down by `q + 1`. -/
theorem componentPerm_torusLink :
    (torusLink p q).componentPerm = (finRotate (p + 1 + (q + 1)) ^ (q + 1))⁻¹ := by
  rw [componentPerm_def, torusLink_O_toPerm, torusLink_X_toPerm, mul_one]

/-- Cancelling the shift out of the grid number inside a greatest common divisor:
`gcd ((p + 1) + (q + 1)) (q + 1) = gcd (p + 1) (q + 1)`. -/
private theorem gcd_torus : (p + 1 + (q + 1)).gcd (q + 1) = (p + 1).gcd (q + 1) := by
  rw [Nat.gcd_comm, Nat.gcd_add_self_right, Nat.gcd_comm]

/-- The components of a standard torus link grid all carry the same number of markings, and there
are `gcd (p + 1) (q + 1)` of them: exactly the number of components of the `(p + 1, q + 1)` torus
link. -/
theorem componentCycleType_torusLink :
    (torusLink p q).componentCycleType =
      Multiset.replicate ((p + 1).gcd (q + 1))
        ((p + 1 + (q + 1)) / (p + 1).gcd (q + 1)) := by
  rw [componentCycleType_def, componentPerm_torusLink, Equiv.Perm.cycleType_inv,
    cycleType_pow_of_isCycle (isCycle_finRotate_torus p q) (not_card_dvd_torus p q),
    card_support_finRotate_torus, gcd_torus]

/-- A standard torus link grid represents a link with `gcd (p + 1) (q + 1)` components. -/
theorem componentCount_torusLink :
    (torusLink p q).componentCount = (p + 1).gcd (q + 1) := by
  rw [componentCount_def, componentCycleType_torusLink, Multiset.card_replicate]

/-- A standard torus link grid represents a knot exactly when its two winding numbers are
coprime. -/
theorem isKnot_torusLink_iff : (torusLink p q).IsKnot ↔ (p + 1).Coprime (q + 1) := by
  rw [isKnot_def, componentCount_torusLink, Nat.Coprime]

/-! ### The smallest members -/

/-- The `5 × 5` grid diagram `torusLink 1 2` of the `(2, 3)` torus knot, the trefoil, represents a
knot. -/
theorem isKnot_torusLink_one_two : (torusLink 1 2).IsKnot := by
  rw [isKnot_torusLink_iff]
  decide

/-- The `4 × 4` grid diagram `torusLink 1 1` of the `(2, 2)` torus link, the Hopf link, represents
a two-component link. -/
theorem componentCount_torusLink_one_one : (torusLink 1 1).componentCount = 2 := by
  rw [componentCount_torusLink]
  decide

/-- The `4 × 4` Hopf link grid does not represent a knot, so the family really does produce
links of more than one component. -/
theorem not_isKnot_torusLink_one_one : ¬(torusLink 1 1).IsKnot := by
  rw [isKnot_torusLink_iff]
  decide

/-- The `6 × 6` grid diagram `torusLink 2 2` of the `(3, 3)` torus link has three components, each
carrying two of its six markings. -/
theorem componentCycleType_torusLink_two_two :
    (torusLink 2 2).componentCycleType = {2, 2, 2} := by
  rw [componentCycleType_torusLink]
  decide

end GridDiagram

end TauCeti
