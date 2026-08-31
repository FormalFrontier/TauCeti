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
abbrev separateNoiseCongr (rowPerm colPerm : Equiv.Perm ℕ) :
    (NoiseIndex Axis (ℕ × ℕ) → I) ≃ᵐ (NoiseIndex Axis (ℕ × ℕ) → I) :=
  noiseCongr (separateVertexPerm rowPerm colPerm) (separateCellPerm rowPerm colPerm)

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
  simp only [separateArray_apply, noiseCongr_apply, indexEquiv_global, indexEquiv_vertex,
    indexEquiv_cell, separateVertexPerm_row, separateVertexPerm_column, separateCellPerm_apply]

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
abbrev jointNoiseCongr (perm : Equiv.Perm ℕ) :
    (NoiseIndex Unit (Sym2 ℕ) → I) ≃ᵐ (NoiseIndex Unit (Sym2 ℕ) → I) :=
  noiseCongr (fun _ : Unit => perm) (jointCellPerm perm)

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
  simp only [jointArray_apply, noiseCongr_apply, indexEquiv_global, indexEquiv_vertex,
    indexEquiv_cell, jointCellPerm_apply, Sym2.map_mk]

end AldousHoover

end Probability

end TauCeti
