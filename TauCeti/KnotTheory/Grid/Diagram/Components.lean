/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import TauCeti.KnotTheory.Grid.Diagram.Relabeling
public import TauCeti.KnotTheory.Grid.Rotation

/-!
# Link components of a grid diagram

The `O`- and `X`-markings of a grid diagram determine an oriented link combinatorially. Starting
at the `O`-marking in column `c`, follow its horizontal segment to the `X`-marking in the same
row, then follow the vertical segment to the `O`-marking in that column. On column labels this is
the permutation

`c ↦ X⁻¹(O(c))`.

Its cycles are exactly the link components. This file packages that permutation, its cycle
decomposition and component count, and the predicate that the represented link is a knot. The
grid-diagram disjointness condition makes the component permutation fixed-point-free, so
Mathlib's cycle decomposition accounts for every marking.

Row relabeling leaves the component permutation unchanged, while column relabeling conjugates it.
Consequently the cycle type, component count, and knot predicate are preserved by both
relabelings, as well as by diagonal reflection, half-turn rotation, and exchanging `O` with `X`.

## Main definitions

* `TauCeti.GridDiagram.componentPerm`: the permutation obtained by following one horizontal and
  one vertical grid segment.
* `TauCeti.GridDiagram.componentCycles`: the cycle factors representing the link components.
* `TauCeti.GridDiagram.componentCycleType`: the multiset of component sizes.
* `TauCeti.GridDiagram.componentCount`: the number of represented link components.
* `TauCeti.GridDiagram.IsKnot`: the represented link has exactly one component.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.1, "Grid diagrams and
grid states", and supplies the knot-versus-link distinction needed by the later knot invariant
`τ` in Lane G.6 and the links stage in Lane G.9. The component traversal follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The permutation of `O`-marking columns obtained by traversing one horizontal segment from
`O` to `X`, then the vertical segment back to `O`.

Thus `componentPerm G c = XColumnOfRow G (G.O c)`. Its permutation cycles are the components of
the oriented link represented by `G`. -/
def componentPerm : Equiv.Perm (Fin n) :=
  G.X.toPerm⁻¹ * G.O.toPerm

/-- Applying the component permutation follows the `O`-marking's row to its unique
`X`-marking column. -/
@[simp]
theorem componentPerm_apply (c : Fin n) :
    G.componentPerm c = XColumnOfRow G (G.O c) :=
  (rfl)

/-- The component permutation has no fixed columns, because an `O` and an `X` cannot occupy the
same square. -/
theorem componentPerm_apply_ne_self (c : Fin n) : G.componentPerm c ≠ c := by
  intro h
  apply G.disjoint c
  simpa [componentPerm] using congrArg (fun d => G.X d) h

/-- Every column belongs to the support of the component permutation. -/
@[simp]
theorem support_componentPerm : G.componentPerm.support = Finset.univ := by
  ext c
  simpa only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true] using
    G.componentPerm_apply_ne_self c

/-- The cycle factors of the component permutation. Each factor is one component of the
represented link, expressed as a cyclic permutation of its `O`-marking columns. -/
def componentCycles : Finset (Equiv.Perm (Fin n)) :=
  G.componentPerm.cycleFactorsFinset

/-- A permutation is a component cycle exactly when it is a cycle agreeing with the component
permutation throughout its support. -/
@[simp]
theorem mem_componentCycles_iff (c : Equiv.Perm (Fin n)) :
    c ∈ G.componentCycles ↔
      c.IsCycle ∧ ∀ a ∈ c.support, c a = G.componentPerm a := by
  rw [componentCycles, Equiv.Perm.mem_cycleFactorsFinset_iff]

/-- The multiset of component sizes of the link represented by a grid diagram. -/
def componentCycleType : Multiset ℕ :=
  G.componentPerm.cycleType

/-- The number of components of the link represented by a grid diagram. -/
def componentCount : ℕ :=
  G.componentCycleType.card

/-- The number of component cycles agrees with `componentCount`. -/
@[simp]
theorem card_componentCycles : G.componentCycles.card = G.componentCount := by
  simp [componentCycles, componentCount, componentCycleType, Equiv.Perm.cycleType_def]

/-- The component sizes sum to the grid size: every marking belongs to exactly one component. -/
@[simp]
theorem sum_componentCycleType : G.componentCycleType.sum = n := by
  rw [componentCycleType, Equiv.Perm.sum_cycleType, support_componentPerm,
    Finset.card_univ, Fintype.card_fin]

/-- A grid diagram represents a knot when its component permutation has exactly one cycle. -/
def IsKnot : Prop :=
  G.componentCount = 1

/-- A grid diagram represents a knot exactly when its component permutation is a single
nontrivial cycle. -/
theorem isKnot_iff_componentPerm_isCycle :
    G.IsKnot ↔ G.componentPerm.IsCycle := by
  rw [IsKnot, componentCount, componentCycleType,
    Equiv.Perm.card_cycleType_eq_one]

/-- The sole component of a knot grid contains all `n` markings. -/
theorem IsKnot.componentCycleType_eq (hG : G.IsKnot) :
    G.componentCycleType = {n} := by
  rw [componentCycleType, (G.isKnot_iff_componentPerm_isCycle.mp hG).cycleType,
    support_componentPerm, Finset.card_univ, Fintype.card_fin]

/-- A grid diagram has no link components exactly when its size is zero. -/
@[simp]
theorem componentCount_eq_zero_iff : G.componentCount = 0 ↔ n = 0 := by
  constructor
  · intro h
    rw [componentCount] at h
    have htype : G.componentCycleType = 0 := Multiset.card_eq_zero.mp h
    simpa [htype] using (G.sum_componentCycleType).symm
  · intro h
    subst n
    rw [componentCount, componentCycleType]
    have hperm : G.componentPerm = 1 := Subsingleton.elim _ _
    simp [hperm]

/-- The empty grid has no link components. -/
@[simp]
theorem componentCount_eq_zero_of_zero (G : GridDiagram 0) :
    G.componentCount = 0 :=
  G.componentCount_eq_zero_iff.mpr rfl

/-- An empty grid does not represent a knot. -/
@[simp]
theorem not_isKnot_of_zero (G : GridDiagram 0) : ¬G.IsKnot := by
  rw [IsKnot, componentCount_eq_zero_of_zero]
  exact Nat.zero_ne_one

/-- Every `2 × 2` grid diagram represents a knot. Its fixed-point-free component permutation is
the transposition of the two columns. -/
@[simp]
theorem isKnot_of_two (G : GridDiagram 2) : G.IsKnot := by
  rw [isKnot_iff_componentPerm_isCycle]
  apply Equiv.Perm.IsSwap.isCycle
  rw [← Equiv.Perm.card_support_eq_two, support_componentPerm,
    Finset.card_univ, Fintype.card_fin]

/-! ### Naturality under grid symmetries -/

/-- Relabeling rows does not change the component permutation: the common row relabeling cancels
between the `O`- and `X`-marking permutations. -/
@[simp]
theorem componentPerm_relabelRows (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).componentPerm = G.componentPerm := by
  ext c
  simp [componentPerm_apply]

/-- Relabeling columns conjugates the component permutation by the column relabeling. -/
theorem componentPerm_relabelColumns (κ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).componentPerm =
      κ * G.componentPerm * κ⁻¹ := by
  ext c
  simp [componentPerm_apply]

/-- Row relabeling preserves the component cycles. -/
@[simp]
theorem componentCycles_relabelRows (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).componentCycles = G.componentCycles := by
  simp [componentCycles]

/-- Column relabeling transports component cycles by conjugation. -/
theorem mem_componentCycles_relabelColumns (κ c : Equiv.Perm (Fin n)) :
    κ * c * κ⁻¹ ∈ (G.relabelColumns κ).componentCycles ↔
      c ∈ G.componentCycles := by
  rw [componentCycles, componentPerm_relabelColumns, componentCycles,
    Equiv.Perm.mem_cycleFactorsFinset_conj]

/-- Row relabeling preserves the component-size multiset. -/
@[simp]
theorem componentCycleType_relabelRows (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).componentCycleType = G.componentCycleType := by
  rw [componentCycleType, componentPerm_relabelRows, componentCycleType]

/-- Column relabeling preserves the component-size multiset. -/
@[simp]
theorem componentCycleType_relabelColumns (κ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).componentCycleType = G.componentCycleType := by
  rw [componentCycleType, componentPerm_relabelColumns, Equiv.Perm.cycleType_conj,
    componentCycleType]

/-- Exchanging the `O`- and `X`-markings inverts the component permutation. -/
@[simp]
theorem componentPerm_swapMarkings :
    G.swapMarkings.componentPerm = G.componentPerm⁻¹ := by
  simp [componentPerm]

/-- Exchanging the marking types reverses every component cycle. -/
theorem mem_componentCycles_swapMarkings (c : Equiv.Perm (Fin n)) :
    c⁻¹ ∈ G.swapMarkings.componentCycles ↔ c ∈ G.componentCycles := by
  rw [componentCycles, componentPerm_swapMarkings, componentCycles]
  have aux : ∀ {g c : Equiv.Perm (Fin n)}, c ∈ g.cycleFactorsFinset →
      c⁻¹ ∈ g⁻¹.cycleFactorsFinset := by
    intro g c hmem
    have hc := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hmem
    rw [Equiv.Perm.mem_cycleFactorsFinset_iff]
    refine ⟨hc.1.inv, ?_⟩
    intro a ha
    rw [Equiv.Perm.support_inv] at ha
    have hga : g⁻¹ a ∈ c.support := by
      rw [← Equiv.Perm.mem_cycleFactorsFinset_support hmem (g⁻¹ a)]
      simpa using ha
    apply c.injective
    simpa using (hc.2 (g⁻¹ a) hga).symm
  refine ⟨fun h ↦ ?_, aux⟩
  simpa using aux (g := G.componentPerm⁻¹) (c := c⁻¹) h

/-- Exchanging the two marking types preserves the component-size multiset. -/
@[simp]
theorem componentCycleType_swapMarkings :
    G.swapMarkings.componentCycleType = G.componentCycleType := by
  rw [componentCycleType, componentPerm_swapMarkings, Equiv.Perm.cycleType_inv,
    componentCycleType]

/-- Diagonal reflection conjugates the inverse component permutation by the `X`-marking
permutation. -/
theorem componentPerm_transpose :
  G.transpose.componentPerm =
      G.X.toPerm * G.componentPerm⁻¹ * G.X.toPerm⁻¹ := by
  ext c
  simp [componentPerm, GridState.transpose]

/-- Diagonal reflection transports component cycles by inversion and conjugation. -/
theorem mem_componentCycles_transpose (c : Equiv.Perm (Fin n)) :
    G.X.toPerm * c⁻¹ * G.X.toPerm⁻¹ ∈ G.transpose.componentCycles ↔
      c ∈ G.componentCycles := by
  rw [componentCycles, componentPerm_transpose,
    Equiv.Perm.mem_cycleFactorsFinset_conj]
  simpa [componentCycles, componentPerm_swapMarkings] using
    G.mem_componentCycles_swapMarkings c

/-- Diagonal reflection preserves the component-size multiset. -/
@[simp]
theorem componentCycleType_transpose :
    G.transpose.componentCycleType = G.componentCycleType := by
  rw [componentCycleType, componentPerm_transpose, Equiv.Perm.cycleType_conj,
    Equiv.Perm.cycleType_inv, componentCycleType]

/-- Half-turn rotation transports component cycles by coordinate-reversal conjugation. -/
theorem mem_componentCycles_rotate (c : Equiv.Perm (Fin n)) :
    Fin.revPerm * c * Fin.revPerm⁻¹ ∈ G.rotate.componentCycles ↔
      c ∈ G.componentCycles := by
  simpa [GridDiagram.rotate] using
    G.mem_componentCycles_relabelColumns Fin.revPerm c

/-- Half-turn rotation preserves the component-size multiset. -/
@[simp]
theorem componentCycleType_rotate :
    G.rotate.componentCycleType = G.componentCycleType := by
  rw [GridDiagram.rotate, componentCycleType_relabelRows, componentCycleType_relabelColumns]

/-- Row relabeling preserves the number of represented link components. -/
@[simp]
theorem componentCount_relabelRows (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).componentCount = G.componentCount := by
  simp [componentCount]

/-- Column relabeling preserves the number of represented link components. -/
@[simp]
theorem componentCount_relabelColumns (κ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).componentCount = G.componentCount := by
  simp [componentCount]

/-- Diagonal reflection preserves the number of represented link components. -/
@[simp]
theorem componentCount_transpose :
    G.transpose.componentCount = G.componentCount := by
  simp [componentCount]

/-- Half-turn rotation preserves the number of represented link components. -/
@[simp]
theorem componentCount_rotate :
    G.rotate.componentCount = G.componentCount := by
  simp [componentCount]

/-- Exchanging the two marking types preserves the number of represented link components. -/
@[simp]
theorem componentCount_swapMarkings :
    G.swapMarkings.componentCount = G.componentCount := by
  simp [componentCount]

/-- Row relabeling preserves whether a grid diagram represents a knot. -/
@[simp]
theorem isKnot_relabelRows (ρ : Equiv.Perm (Fin n)) :
    (G.relabelRows ρ).IsKnot ↔ G.IsKnot := by
  simp [IsKnot]

/-- Column relabeling preserves whether a grid diagram represents a knot. -/
@[simp]
theorem isKnot_relabelColumns (κ : Equiv.Perm (Fin n)) :
    (G.relabelColumns κ).IsKnot ↔ G.IsKnot := by
  simp [IsKnot]

/-- Diagonal reflection preserves whether a grid diagram represents a knot. -/
@[simp]
theorem isKnot_transpose : G.transpose.IsKnot ↔ G.IsKnot := by
  simp [IsKnot]

/-- Half-turn rotation preserves whether a grid diagram represents a knot. -/
@[simp]
theorem isKnot_rotate : G.rotate.IsKnot ↔ G.IsKnot := by
  simp [IsKnot]

/-- Exchanging the two marking types preserves whether a grid diagram represents a knot. -/
@[simp]
theorem isKnot_swapMarkings : G.swapMarkings.IsKnot ↔ G.IsKnot := by
  simp [IsKnot]

end GridDiagram

end TauCeti
