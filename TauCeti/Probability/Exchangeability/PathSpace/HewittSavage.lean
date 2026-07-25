/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Exchangeable.Sigma
public import Mathlib.Probability.Independence.ZeroOne
-- Non-public: used only inside proofs.
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent

/-!
# The Hewitt–Savage zero-one law

Work in progress.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

namespace Probability

/-- The finitely supported permutation of `ℕ` that swaps the block `[0, N)` with `[N, 2N)`
pointwise and fixes everything from `2 * N` on. -/
def blockSwap (N : ℕ) : Equiv.Perm ℕ :=
  Equiv.Perm.viaFintypeEmbedding
    (((finSumFinEquiv (m := N) (n := N)).symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv)
    ⟨Fin.val, Fin.val_injective⟩

theorem blockSwap_apply_of_lt {N i : ℕ} (hi : i < N) : blockSwap N i = N + i := by
  have key : ((finSumFinEquiv.symm.trans (Equiv.sumComm (Fin N) (Fin N))).trans finSumFinEquiv)
      (Fin.castAdd N ⟨i, hi⟩) = Fin.natAdd N ⟨i, hi⟩ := by
    rw [Equiv.trans_apply, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
    rfl
  have h : (⟨Fin.val, Fin.val_injective⟩ : Fin (N + N) ↪ ℕ)
      (Fin.castAdd N ⟨i, hi⟩) = i := rfl
  rw [blockSwap, ← h, Equiv.Perm.viaFintypeEmbedding_apply_image, key]
  rfl

theorem blockSwap_apply_of_le {N n : ℕ} (hn : N + N ≤ n) : blockSwap N n = n := by
  refine Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ ?_
  rintro ⟨j, rfl⟩
  exact absurd j.isLt (not_lt.mpr hn)

/-- `blockSwap N` carries any index block inside `[0, N)` off itself: the moved copy lands in
`[N, 2N)`. This is the disjointness the independence step consumes. -/
theorem disjoint_map_blockSwap {N : ℕ} {F : Finset ℕ} (hF : F ⊆ Finset.range N) :
    Disjoint F (F.map (Equiv.toEmbedding (blockSwap N))) := by
  rw [Finset.disjoint_left]
  intro a haF hamem
  obtain ⟨b, hbF, hb⟩ := Finset.mem_map.mp hamem
  have hbN : b < N := Finset.mem_range.mp (hF hbF)
  have haN : a < N := Finset.mem_range.mp (hF haF)
  rw [Equiv.coe_toEmbedding, blockSwap_apply_of_lt hbN] at hb
  omega

theorem blockSwap_finite_support (N : ℕ) :
    (MulAction.fixedBy ℕ (blockSwap N))ᶜ.Finite := by
  refine Set.Finite.subset (Set.finite_Iio (N + N)) ?_
  intro n hn
  by_contra hmem
  exact hn (blockSwap_apply_of_le (not_lt.mp hmem))

section Cylinder

variable {α : Type*}

/-- Read a block indexed by the moved index set `F.map π` back onto `F`, along `π`. This is the
change of variables that turns a `π`-reindexed cylinder over `F` into a cylinder over `F.map π`. -/
@[expose]
def pullMoved (π : Equiv.Perm ℕ) (F : Finset ℕ) (α : Type*)
    (g : ∀ _j : F.map (Equiv.toEmbedding π), α) : ∀ _i : F, α :=
  fun i => g ⟨π ↑i, Finset.mem_map_of_mem _ i.2⟩

@[simp]
theorem pullMoved_apply (π : Equiv.Perm ℕ) (F : Finset ℕ)
    (g : ∀ _j : F.map (Equiv.toEmbedding π), α) (i : F) :
    pullMoved π F α g i = g ⟨π ↑i, Finset.mem_map_of_mem _ i.2⟩ :=
  rfl

/-- Reindexing a cylinder over `F` by `π` is a cylinder over the moved index set `F.map π`: both
sides say that the coordinates `p (π i)`, for `i ∈ F`, lie in `S`. -/
theorem preimage_permReindex_cylinder (π : Equiv.Perm ℕ) (F : Finset ℕ)
    (S : Set (∀ _i : F, α)) :
    permReindex (α := α) π ⁻¹' cylinder F S
      = cylinder (F.map (Equiv.toEmbedding π)) (pullMoved π F α ⁻¹' S) :=
  rfl

@[fun_prop]
theorem measurable_pullMoved [MeasurableSpace α] (π : Equiv.Perm ℕ) (F : Finset ℕ) :
    Measurable (pullMoved π F α) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Every measurable path-space event is approximated, in measure, by a measurable cylinder over a
finite index set. -/
theorem exists_cylinder_measure_symmDiff_lt [MeasurableSpace α] {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] {s : Set (ℕ → α)} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (F : Finset ℕ) (S : Set (∀ _i : F, α)),
      MeasurableSet S ∧ ρ (symmDiff (cylinder F S) s) < ε := by
  have hcov : ∃ D : Set (Set (ℕ → α)), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : ℕ => α) ∧ ρ (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · rintro u (rfl : u = Set.univ)
      rw [← cylinder_univ (∅ : Finset ℕ)]
      exact cylinder_mem_measurableCylinders _ _ MeasurableSet.univ
    · simp
  obtain ⟨t, ht_mem, ht⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := ρ)
    isSetRing_measurableCylinders hcov generateFrom_measurableCylinders.symm hs hε
  obtain ⟨F, S, hS, rfl⟩ := (mem_measurableCylinders t).mp ht_mem
  exact ⟨F, S, hS, ht⟩

end Cylinder

end Probability

end TauCeti
