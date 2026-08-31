/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover

/-!
# The noise action for Aldous--Hoover codings

The invariance proofs for the Aldous--Hoover codings reindex the independent noise coordinates.
This file names those reindexings and records their pathwise effect on the coded array.  The
separate action permutes the row and column vertex families independently, while the joint action
uses one permutation on both vertex families and on the unordered-pair cell family.

The resulting identities are the reusable symmetry interface for the converse representation:
they expose the exact measurable change of noise variables behind the law-level exchangeability
theorems in `Arrays.AldousHoover`, without identifying a coding function for an arbitrary
exchangeable array.  In particular, the cell action in the joint case is `Sym2.map`, so it
preserves the unordered cell shared by the two orientations of an off-diagonal entry.

## Main declarations

* `AldousHoover.separateNoiseCongr` and `AldousHoover.jointNoiseCongr` are the measurable noise
  equivalences for the two coding forms;
* `AldousHoover.separateArray_reindex` and `AldousHoover.jointArray_reindex` give their pathwise
  equivariance formulas;
* `AldousHoover.map_separateNoiseCongr_noiseMeasure` and
  `AldousHoover.map_jointNoiseCongr_noiseMeasure` record preservation of the canonical noise law.

The definitions and the law-level exchangeability results are in `Arrays.AldousHoover`; this
module only packages the common action interface used by later converse constructions.

## References

* David Aldous, ["Representations for partially exchangeable arrays of random variables"]
  (https://doi.org/10.1016/0047-259X(81)90099-3), *Journal of Multivariate Analysis* 11
  (1981), 581--598.
* Olav Kallenberg, [*Probabilistic Symmetries and Invariance Principles*]
  (https://doi.org/10.1007/0-387-28836-4), Springer (2005), Chapter 7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti

namespace Probability

namespace AldousHoover

/-! ## Separate exchangeability -/

/-- The action on the two vertex-noise families associated to two axis permutations. -/
def separateVertexPerm (rowPerm colPerm : Equiv.Perm ℕ) : Axis → Equiv.Perm ℕ
  | .row => rowPerm
  | .column => colPerm

@[simp]
theorem separateVertexPerm_row (rowPerm colPerm : Equiv.Perm ℕ) :
    separateVertexPerm rowPerm colPerm .row = rowPerm :=
  by simp [separateVertexPerm]

@[simp]
theorem separateVertexPerm_column (rowPerm colPerm : Equiv.Perm ℕ) :
    separateVertexPerm rowPerm colPerm .column = colPerm :=
  by simp [separateVertexPerm]

/-- The action on cell-noise coordinates associated to two axis permutations. -/
def separateCellPerm (rowPerm colPerm : Equiv.Perm ℕ) : ℕ × ℕ ≃ ℕ × ℕ :=
  rowPerm.prodCongr colPerm

@[simp]
theorem separateCellPerm_apply (rowPerm colPerm : Equiv.Perm ℕ) (p : ℕ × ℕ) :
    separateCellPerm rowPerm colPerm p = (rowPerm p.1, colPerm p.2) :=
  by simp [separateCellPerm, Prod.map]

/-- The measurable equivalence reindexing the separate-coding noise by two axis permutations. -/
def separateNoiseCongr (rowPerm colPerm : Equiv.Perm ℕ) :
    (NoiseIndex Axis (ℕ × ℕ) → I) ≃ᵐ (NoiseIndex Axis (ℕ × ℕ) → I) :=
  noiseCongr (separateVertexPerm rowPerm colPerm) (separateCellPerm rowPerm colPerm)

@[simp]
theorem separateNoiseCongr_apply_global (rowPerm colPerm : Equiv.Perm ℕ)
    (u : NoiseIndex Axis (ℕ × ℕ) → I) :
    separateNoiseCongr rowPerm colPerm u .global = u .global := by
  simp [separateNoiseCongr]

@[simp]
theorem separateNoiseCongr_apply_vertex (rowPerm colPerm : Equiv.Perm ℕ)
    (u : NoiseIndex Axis (ℕ × ℕ) → I) (a : Axis) (i : ℕ) :
    separateNoiseCongr rowPerm colPerm u (.vertex a i) =
      u (.vertex a ((separateVertexPerm rowPerm colPerm a) i)) := by
  simp [separateNoiseCongr]

@[simp]
theorem separateNoiseCongr_apply_cell (rowPerm colPerm : Equiv.Perm ℕ)
    (u : NoiseIndex Axis (ℕ × ℕ) → I) (p : ℕ × ℕ) :
    separateNoiseCongr rowPerm colPerm u (.cell p) =
      u (.cell (separateCellPerm rowPerm colPerm p)) := by
  simp [separateNoiseCongr]

/-- The separate noise reindexing preserves the canonical independent-uniform noise law. -/
theorem map_separateNoiseCongr_noiseMeasure (rowPerm colPerm : Equiv.Perm ℕ) :
    (noiseMeasure Axis (ℕ × ℕ)).map (separateNoiseCongr rowPerm colPerm) =
      noiseMeasure Axis (ℕ × ℕ) :=
  map_noiseCongr_noiseMeasure _ _

/-- Pathwise equivariance of the separate coding under the corresponding noise reindexing. -/
theorem separateArray_reindex (f : I × I × I × I → α)
    (rowPerm colPerm : Equiv.Perm ℕ) (u : NoiseIndex Axis (ℕ × ℕ) → I)
    (p : ℕ × ℕ) :
    separateArray f (rowPerm p.1, colPerm p.2) u =
      separateArray f p (separateNoiseCongr rowPerm colPerm u) := by
  simp only [separateArray_apply, separateNoiseCongr_apply_global,
    separateNoiseCongr_apply_vertex, separateNoiseCongr_apply_cell, separateVertexPerm_row,
    separateVertexPerm_column, separateCellPerm_apply]

/-! ## Joint exchangeability -/

/-- The action on unordered-pair cell indices associated to a permutation of the vertex indices. -/
def jointCellPerm (perm : Equiv.Perm ℕ) : Sym2 ℕ ≃ Sym2 ℕ where
  toFun := Sym2.map perm
  invFun := Sym2.map perm.symm
  left_inv p := by simp [Sym2.map_map]
  right_inv p := by simp [Sym2.map_map]

@[simp]
theorem jointCellPerm_apply (perm : Equiv.Perm ℕ) (p : Sym2 ℕ) :
    jointCellPerm perm p = Sym2.map perm p :=
  by simp [jointCellPerm]

/-- The measurable equivalence reindexing the joint-coding noise by one vertex permutation. -/
def jointNoiseCongr (perm : Equiv.Perm ℕ) :
    (NoiseIndex Unit (Sym2 ℕ) → I) ≃ᵐ (NoiseIndex Unit (Sym2 ℕ) → I) :=
  noiseCongr (fun _ : Unit => perm) (jointCellPerm perm)

@[simp]
theorem jointNoiseCongr_apply_global (perm : Equiv.Perm ℕ)
    (u : NoiseIndex Unit (Sym2 ℕ) → I) :
    jointNoiseCongr perm u .global = u .global := by
  simp [jointNoiseCongr]

@[simp]
theorem jointNoiseCongr_apply_vertex (perm : Equiv.Perm ℕ)
    (u : NoiseIndex Unit (Sym2 ℕ) → I) (i : ℕ) :
    jointNoiseCongr perm u (.vertex () i) = u (.vertex () (perm i)) := by
  simp [jointNoiseCongr]

@[simp]
theorem jointNoiseCongr_apply_cell (perm : Equiv.Perm ℕ)
    (u : NoiseIndex Unit (Sym2 ℕ) → I) (p : Sym2 ℕ) :
    jointNoiseCongr perm u (.cell p) = u (.cell (jointCellPerm perm p)) := by
  simp [jointNoiseCongr]

/-- The joint noise reindexing preserves the canonical independent-uniform noise law. -/
theorem map_jointNoiseCongr_noiseMeasure (perm : Equiv.Perm ℕ) :
    (noiseMeasure Unit (Sym2 ℕ)).map (jointNoiseCongr perm) =
      noiseMeasure Unit (Sym2 ℕ) :=
  map_noiseCongr_noiseMeasure _ _

/-- Pathwise equivariance of the joint coding under the corresponding noise reindexing. -/
theorem jointArray_reindex (f : I × I × I × I → α)
    (perm : Equiv.Perm ℕ) (u : NoiseIndex Unit (Sym2 ℕ) → I)
    (p : ℕ × ℕ) :
    jointArray f (perm p.1, perm p.2) u =
      jointArray f p (jointNoiseCongr perm u) := by
  simp only [jointArray_apply, jointNoiseCongr_apply_global, jointNoiseCongr_apply_vertex,
    jointNoiseCongr_apply_cell, jointCellPerm_apply, Sym2.map_mk]

end AldousHoover

end Probability

end TauCeti
