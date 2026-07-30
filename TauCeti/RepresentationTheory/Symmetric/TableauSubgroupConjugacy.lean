/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.RepresentationTheory.Symmetric.RowColumnSubgroup
public import TauCeti.RepresentationTheory.Symmetric.YoungSubgroup

/-!
# Tableau row groups and Young subgroups

The row group of a tableau depends on its labeling, whereas the Young subgroup attached to its
shape uses consecutive blocks. This file constructs the permutation sending the consecutive-block
labeling to a given tableau and proves that it conjugates the corresponding Young subgroup onto
the tableau's row group.

## References

* [G. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 3.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 1.
-/

public section

namespace TauCeti

namespace YoungTableau

private noncomputable abbrev shapePartition (μ : YoungDiagram) : μ.card.Partition :=
  (partitionEquivYoungDiagram μ.card).symm ⟨μ, rfl⟩

private theorem shapePartition_sortedParts (μ : YoungDiagram) :
    (shapePartition μ).parts.sort (· ≥ ·) = μ.rowLens := by
  have h := partitionEquivYoungDiagram_apply_rowLens μ.card (shapePartition μ)
  simpa only [shapePartition, Equiv.apply_symm_apply] using h.symm

private abbrev rowBlocks (l : List ℕ) : Type :=
  Σ i : Fin l.length, Fin (l.get i)

private noncomputable def rowCellsEquiv (μ : YoungDiagram) :
    rowBlocks μ.rowLens ≃ ↥μ.cells where
  toFun x := ⟨(x.1, x.2), by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
    rw [← YoungDiagram.get_rowLens]
    exact x.2.2⟩
  invFun c :=
    ⟨⟨c.1.1, by
      rw [YoungDiagram.length_rowLens]
      exact (_root_.YoungDiagram.mem_iff_lt_colLen.mp c.2).trans_le
        (μ.colLen_anti 0 c.1.2 c.1.2.zero_le)⟩,
      ⟨c.1.2, by
        have hj := _root_.YoungDiagram.mem_iff_lt_rowLen.mp c.2
        rw [← YoungDiagram.get_rowLens] at hj
        exact hj⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def sortedBlocksEquivRows (μ : YoungDiagram) :
    rowBlocks ((shapePartition μ).parts.sort (· ≥ ·)) ≃ rowBlocks μ.rowLens :=
  Equiv.cast (congrArg rowBlocks (shapePartition_sortedParts μ))

private theorem cast_rowBlocks_fst {l₁ l₂ : List ℕ} (h : l₁ = l₂)
    (x : rowBlocks l₁) :
    ((Equiv.cast (congrArg rowBlocks h) x).1 : ℕ) = x.1 := by
  subst l₂
  rfl

private theorem cast_rowBlocks_snd {l₁ l₂ : List ℕ} (h : l₁ = l₂)
    (x : rowBlocks l₁) :
    ((Equiv.cast (congrArg rowBlocks h) x).2 : ℕ) = x.2 := by
  subst l₂
  rfl

private theorem sortedBlocksEquivRows_fst (μ : YoungDiagram)
    (x : rowBlocks ((shapePartition μ).parts.sort (· ≥ ·))) :
    ((sortedBlocksEquivRows μ x).1 : ℕ) = x.1 :=
  cast_rowBlocks_fst (shapePartition_sortedParts μ) x

private theorem sortedBlocksEquivRows_snd (μ : YoungDiagram)
    (x : rowBlocks ((shapePartition μ).parts.sort (· ≥ ·))) :
    ((sortedBlocksEquivRows μ x).2 : ℕ) = x.2 :=
  cast_rowBlocks_snd (shapePartition_sortedParts μ) x

/-- The permutation carrying the consecutive-block labeling of a Young diagram to the labeling
of `t`. It sends each block of the shape partition to the correspondingly numbered row of `t`. -/
noncomputable def rowYoungConjugator {μ : YoungDiagram} (t : YoungTableau μ) :
    Equiv.Perm (Fin μ.card) :=
  (youngBlocksEquiv (shapePartition μ)).symm |>.trans <|
    (sortedBlocksEquivRows μ).trans ((rowCellsEquiv μ).trans t)

/-- The row of a label after applying `rowYoungConjugator t` is its consecutive-block number. -/
@[simp]
theorem rowIndex_rowYoungConjugator {μ : YoungDiagram} (t : YoungTableau μ)
    (k : Fin μ.card) :
    rowIndex t (rowYoungConjugator t k) =
      youngBlock ((partitionEquivYoungDiagram μ.card).symm ⟨μ, rfl⟩) k := by
  let x := (youngBlocksEquiv (shapePartition μ)).symm k
  have hk : youngBlocksEquiv (shapePartition μ) x = k :=
    Equiv.apply_symm_apply _ k
  rw [← hk, youngBlock_youngBlocksEquiv]
  simp only [rowYoungConjugator, Equiv.trans_apply, rowIndex_apply, rowCellsEquiv,
    Equiv.symm_apply_apply, x]
  exact sortedBlocksEquivRows_fst μ x

/-- On consecutive-block coordinates, `rowYoungConjugator t` sends position `j` in block `i`
to the label in position `j` of row `i` of `t`. -/
@[simp]
theorem rowYoungConjugator_youngBlocksEquiv {μ : YoungDiagram} (t : YoungTableau μ)
    (x : Σ i : Fin
        (((partitionEquivYoungDiagram μ.card).symm ⟨μ, rfl⟩).parts.sort (· ≥ ·)).length,
      Fin ((((partitionEquivYoungDiagram μ.card).symm ⟨μ, rfl⟩).parts.sort (· ≥ ·)).get i)) :
    rowYoungConjugator t
        (youngBlocksEquiv ((partitionEquivYoungDiagram μ.card).symm ⟨μ, rfl⟩) x) =
      t ⟨(x.1, x.2), by
        rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
        let y := sortedBlocksEquivRows μ x
        calc
          (x.2 : ℕ) = y.2 := (sortedBlocksEquivRows_snd μ x).symm
          _ < μ.rowLens.get y.1 := y.2.2
          _ = μ.rowLen y.1 := YoungDiagram.get_rowLens
          _ = μ.rowLen x.1 := congrArg μ.rowLen (sortedBlocksEquivRows_fst μ x)⟩ := by
  simp only [rowYoungConjugator, Equiv.trans_apply, Equiv.symm_apply_apply]
  apply congrArg t
  apply Subtype.ext
  apply Prod.ext
  · exact sortedBlocksEquivRows_fst μ x
  · exact sortedBlocksEquivRows_snd μ x

/-- Conjugation by `rowYoungConjugator t` carries the Young subgroup of the shape partition
onto the row group of `t`. -/
theorem youngSubgroup_map_conj_eq_rowSubgroup {μ : YoungDiagram} (t : YoungTableau μ) :
    (youngSubgroup ((partitionEquivYoungDiagram μ.card).symm ⟨μ, rfl⟩)).map
        (MulAut.conj (rowYoungConjugator t)).toMonoidHom = rowSubgroup t := by
  rw [youngSubgroup_eq_fiberSubgroup, rowSubgroup_def]
  apply fiberSubgroup_map_conj
  intro a b
  simp only [rowIndex_rowYoungConjugator]
  exact Fin.ext_iff

/-- Conjugation by `rowYoungConjugator t` as a multiplicative equivalence from the Young
subgroup of the shape partition to the row group of `t`. -/
noncomputable def youngSubgroupConjMulEquiv {μ : YoungDiagram} (t : YoungTableau μ) :
    youngSubgroup ((partitionEquivYoungDiagram μ.card).symm ⟨μ, rfl⟩) ≃*
      rowSubgroup t :=
  ((MulAut.conj (rowYoungConjugator t)).subgroupMap
      (youngSubgroup ((partitionEquivYoungDiagram μ.card).symm ⟨μ, rfl⟩))).trans
    (MulEquiv.subgroupCongr (youngSubgroup_map_conj_eq_rowSubgroup t))

/-- The subgroup equivalence acts by conjugation with `rowYoungConjugator t`. -/
@[simp]
theorem youngSubgroupConjMulEquiv_apply_coe {μ : YoungDiagram} (t : YoungTableau μ)
    (σ : youngSubgroup ((partitionEquivYoungDiagram μ.card).symm ⟨μ, rfl⟩)) :
    ((youngSubgroupConjMulEquiv t σ : rowSubgroup t) : Equiv.Perm (Fin μ.card)) =
      rowYoungConjugator t * σ * (rowYoungConjugator t)⁻¹ :=
  by simp [youngSubgroupConjMulEquiv, MulAut.conj_apply]

/-- The inverse subgroup equivalence acts by conjugation with the inverse of
`rowYoungConjugator t`. -/
@[simp]
theorem youngSubgroupConjMulEquiv_symm_apply_coe {μ : YoungDiagram} (t : YoungTableau μ)
    (τ : rowSubgroup t) :
    (((youngSubgroupConjMulEquiv t).symm τ :
        youngSubgroup ((partitionEquivYoungDiagram μ.card).symm ⟨μ, rfl⟩)) :
      Equiv.Perm (Fin μ.card)) =
      (rowYoungConjugator t)⁻¹ * τ * rowYoungConjugator t := by
  simp [youngSubgroupConjMulEquiv]

end YoungTableau

end TauCeti
