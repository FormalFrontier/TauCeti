/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Ring
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.Range
public import TauCeti.Combinatorics.Young.PieriCount
public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.Combinatorics.Young.StandardTableau.Corner

/-!
# The dual Pieri rule for standard Young tableaux

Fix a shape `ν` with `k` cells.  Summing the number of standard Young tableaux over the shapes
`μ` with `n` cells that `ν` interlaces — that is, those containing `ν` with `μ / ν` a horizontal
strip — gives

`∑_{μ ⊢ n, ν ≺ μ} f^μ = C(n, k) · f^ν`

(`TauCeti.sum_standardCount_interlacedBy`).  This is the Pieri rule `s_ν · h_{n-k} = ∑ s_μ`
evaluated under the specialization that sends a Schur function `s_μ` of degree `n` to `f^μ / n!`,
but it is proved here directly, by induction on `n`.

The induction expands `f^μ` along the corners of `μ` (`TauCeti.standardCount_eq_sum_corners`),
which turns the sum into a sum over the shapes `ρ` with `n - 1` cells of `f^ρ` weighted by the
number of cells addable to `ρ` keeping `ν` interlacing.  That weight is counted by
`YoungDiagram.card_filter_addableCells_interlacedBy`: it is one more than the number of corners of
`ν` whose deletion leaves a shape interlaced by `ρ`, when `ν` interlaces `ρ`, and equal to it
otherwise.  The first part reproduces the inductive hypothesis at `ν`, the second reproduces it at
each `ν` minus a corner, and `C(n-1, k) + C(n-1, k-1) = C(n, k)` closes the induction.

## Main definitions

* `TauCeti.shapesOfSize`: the Young diagrams with a given number of cells, as a `Finset`.
* `TauCeti.shapesOfSizeLE`: the Young diagrams with at most a given number of cells.

## Main results

* `TauCeti.sum_standardCount_interlacedBy`: the dual Pieri rule.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 4.9.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 8: Schur-Weyl duality
-/

public section

namespace TauCeti

open YoungDiagram

/-! ### The shapes of a given size -/

/-- A diagram with no cells is empty. -/
theorem YoungDiagram.eq_bot_of_card_eq_zero {μ : YoungDiagram} (h : μ.card = 0) : μ = ⊥ := by
  have hcells : μ.cells = ∅ := Finset.card_eq_zero.mp h
  ext d
  rw [hcells]
  simp

/-- A diagram all of whose rows are empty is empty. -/
theorem YoungDiagram.eq_bot_of_forall_rowLen_eq_zero {μ : YoungDiagram}
    (h : ∀ i, μ.rowLen i = 0) : μ = ⊥ := by
  ext d
  simp only [_root_.YoungDiagram.mem_cells]
  refine ⟨fun hd => ?_, fun hd => absurd hd (by simp)⟩
  have := _root_.YoungDiagram.mem_iff_lt_rowLen.mp hd
  rw [h d.1] at this
  omega

@[simp]
theorem YoungDiagram.rowLen_bot (i : ℕ) : (⊥ : YoungDiagram).rowLen i = 0 :=
  _root_.YoungDiagram.rowLen_eq_of_mem (by omega) (by simp)

/-- There are finitely many shapes with a given number of cells: they are the Young diagrams of
the partitions of that number. -/
theorem finite_setOf_card_eq (n : ℕ) : {μ : YoungDiagram | μ.card = n}.Finite := by
  have hrange : {μ : YoungDiagram | μ.card = n} = Set.range (diagramOf (n := n)) := by
    ext μ
    exact ⟨fun hμ => ⟨toPartition μ hμ, diagramOf_toPartition μ hμ⟩,
      fun ⟨p, hp⟩ => hp ▸ card_diagramOf p⟩
  rw [hrange]
  exact Set.finite_range _

/-- **The shapes with `n` cells**, as a `Finset`. -/
noncomputable def shapesOfSize (n : ℕ) : Finset YoungDiagram :=
  (finite_setOf_card_eq n).toFinset

@[simp]
theorem mem_shapesOfSize {n : ℕ} {μ : YoungDiagram} : μ ∈ shapesOfSize n ↔ μ.card = n :=
  Set.Finite.mem_toFinset _

theorem shapesOfSize_zero : shapesOfSize 0 = {⊥} := by
  ext μ
  rw [mem_shapesOfSize, Finset.mem_singleton]
  exact ⟨YoungDiagram.eq_bot_of_card_eq_zero, fun h => by simp [h]⟩

/-- There are finitely many shapes with at most `n` cells. -/
theorem finite_setOf_card_le (n : ℕ) : {μ : YoungDiagram | μ.card ≤ n}.Finite := by
  have hunion : {μ : YoungDiagram | μ.card ≤ n}
      = ⋃ k ∈ Set.Iic n, {μ : YoungDiagram | μ.card = k} := by
    ext μ
    simp
  rw [hunion]
  exact Set.Finite.biUnion (Set.toFinite (Set.Iic n)) fun k _ => finite_setOf_card_eq k

/-- **The shapes with at most `n` cells**, as a `Finset`. -/
noncomputable def shapesOfSizeLE (n : ℕ) : Finset YoungDiagram :=
  (finite_setOf_card_le n).toFinset

@[simp]
theorem mem_shapesOfSizeLE {n : ℕ} {μ : YoungDiagram} : μ ∈ shapesOfSizeLE n ↔ μ.card ≤ n :=
  Set.Finite.mem_toFinset _

/-- Splitting the shapes with at most `n` cells according to their number of cells. -/
theorem sum_shapesOfSizeLE {M : Type*} [AddCommMonoid M] (n : ℕ) (g : YoungDiagram → M) :
    ∑ ν ∈ shapesOfSizeLE n, g ν = ∑ k ∈ Finset.range (n + 1), ∑ ν ∈ shapesOfSize k, g ν := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun ν => ν.card) (t := Finset.range (n + 1))
    (fun ν hν => Finset.mem_range.mpr (by have := mem_shapesOfSizeLE.mp hν; omega)) g]
  refine Finset.sum_congr rfl fun k hk => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ν
  rw [Finset.mem_filter, mem_shapesOfSizeLE, mem_shapesOfSize]
  have := Finset.mem_range.mp hk
  omega

/-! ### The dual Pieri rule -/

/-- **The dual Pieri rule**: the standard Young tableaux of the shapes with `n` cells that `ν`
interlaces are `C(n, |ν|)` times as many as those of `ν`. -/
theorem sum_standardCount_interlacedBy (n : ℕ) (ν : YoungDiagram) :
    ∑ μ ∈ (shapesOfSize n).filter fun μ => InterlacedBy μ ν, standardCount μ
      = n.choose ν.card * standardCount ν := by
  induction n generalizing ν with
  | zero =>
    by_cases hν : ν = ⊥
    · subst hν
      have hI : InterlacedBy (⊥ : YoungDiagram) ⊥ := interlacedBy_iff.mpr fun i => by simp
      rw [shapesOfSize_zero, Finset.filter_singleton, ite_eq_left hI, Finset.sum_singleton,
        show (⊥ : YoungDiagram).card = 0 by simp]
      simp
    · have hI : ¬ InterlacedBy (⊥ : YoungDiagram) ν := fun hI =>
        hν (YoungDiagram.eq_bot_of_forall_rowLen_eq_zero fun i =>
          Nat.le_zero.mp (by simpa using hI.rowLen_le i))
      have hcard : ν.card ≠ 0 := fun h => hν (YoungDiagram.eq_bot_of_card_eq_zero h)
      rw [shapesOfSize_zero, Finset.filter_singleton, ite_eq_right hI, Finset.sum_empty,
        Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  | succ n ih =>
    -- Expand along the corners and reindex by the cell added to the smaller shape.
    have hexpand :
        ∑ μ ∈ (shapesOfSize (n + 1)).filter fun μ => InterlacedBy μ ν, standardCount μ
          = ∑ ρ ∈ shapesOfSize n,
              ∑ _c ∈ (addableCells ρ).filter fun c => InterlacedBy (addBox ρ c) ν,
                standardCount ρ := by
      rw [Finset.sum_congr rfl (g := fun μ => ∑ c ∈ corners μ, standardCount (erase μ c))
        (fun μ hμ => standardCount_eq_sum_corners (by
          have := mem_shapesOfSize.mp (Finset.mem_filter.mp hμ).1
          omega))]
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_nbij' (fun x => ⟨erase x.1 x.2, x.2⟩) (fun y => ⟨addBox y.1 y.2, y.2⟩)
        ?_ ?_ ?_ ?_ ?_
      · rintro ⟨μ, c⟩ hx
        simp only [Finset.mem_sigma, Finset.mem_filter, mem_shapesOfSize] at hx
        obtain ⟨⟨hcard, hint⟩, hc⟩ := hx
        have hcor : IsCorner μ c := mem_corners.mp hc
        simp only [Finset.mem_sigma, Finset.mem_filter, mem_shapesOfSize, mem_addableCells]
        refine ⟨?_, hcor.isAddable_erase, ?_⟩
        · have := hcor.card_erase
          omega
        · rw [hcor.addBox_erase]
          exact hint
      · rintro ⟨ρ, c⟩ hy
        rw [Finset.mem_sigma, Finset.mem_filter, mem_addableCells] at hy
        obtain ⟨hρ, hadd, hint⟩ := hy
        rw [Finset.mem_sigma, Finset.mem_filter, mem_shapesOfSize]
        refine ⟨⟨?_, hint⟩, mem_corners.mpr hadd.isCorner_addBox⟩
        rw [hadd.card_addBox, mem_shapesOfSize.mp hρ]
      · rintro ⟨μ, c⟩ hx
        rw [Finset.mem_sigma] at hx
        have hcor : IsCorner μ c := mem_corners.mp hx.2
        simp only [hcor.addBox_erase]
      · rintro ⟨ρ, c⟩ hy
        rw [Finset.mem_sigma, Finset.mem_filter, mem_addableCells] at hy
        simp only [hy.2.1.erase_addBox]
      · rintro ⟨μ, c⟩ -
        rfl
    rw [hexpand]
    -- Count the cells that may be added, row by row.
    have hcount : ∀ ρ ∈ shapesOfSize n,
        ∑ _c ∈ (addableCells ρ).filter fun c => InterlacedBy (addBox ρ c) ν, standardCount ρ
          = (if InterlacedBy ρ ν then standardCount ρ else 0)
            + ∑ c ∈ corners ν, if InterlacedBy ρ (erase ν c) then standardCount ρ else 0 := by
      intro ρ _
      rw [Finset.sum_const, smul_eq_mul, card_filter_addableCells_interlacedBy ρ ν,
        add_mul, Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
        mul_zero, add_zero]
      congr 1
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hcount, Finset.sum_add_distrib, ← Finset.sum_filter,
      Finset.sum_comm]
    have hsecond : ∀ c ∈ corners ν,
        ∑ ρ ∈ shapesOfSize n, (if InterlacedBy ρ (erase ν c) then standardCount ρ else 0)
          = n.choose (erase ν c).card * standardCount (erase ν c) := by
      intro c _
      rw [← Finset.sum_filter]
      exact ih (erase ν c)
    rw [Finset.sum_congr rfl hsecond, ih ν]
    -- Assemble the two binomial coefficients.
    rcases Nat.eq_zero_or_pos ν.card with hzero | hpos
    · have hbot : ν = ⊥ := YoungDiagram.eq_bot_of_card_eq_zero hzero
      have hcorners : corners ν = ∅ := by
        rw [hbot]
        refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
        exact absurd (mem_corners.mp hc).mem (by simp)
      rw [hcorners, Finset.sum_empty, hzero]
      simp
    · obtain ⟨m, hm⟩ : ∃ m, ν.card = m + 1 := ⟨ν.card - 1, by omega⟩
      have hcard : ∀ c ∈ corners ν, (erase ν c).card = m := by
        intro c hc
        have := (mem_corners.mp hc).card_erase
        omega
      have hterm : ∀ c ∈ corners ν, n.choose (erase ν c).card * standardCount (erase ν c)
          = n.choose m * standardCount (erase ν c) := by
        intro c hc
        rw [hcard c hc]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        ← standardCount_eq_sum_corners (by omega), hm, Nat.choose_succ_succ']
      ring

end TauCeti
