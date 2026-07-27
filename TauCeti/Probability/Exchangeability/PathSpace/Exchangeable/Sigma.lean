/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.GroupAction.FiniteSupportPerm
public import TauCeti.Probability.Exchangeability.Basic
public import TauCeti.Probability.Process.Tail.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants

/-!
# Exchangeable σ-algebra on path space

This file records the Layer 2 exchangeability-roadmap σ-algebra of path-space events invariant
under finitely supported permutations of the time coordinate.  It also relates the one-sided path
tail σ-algebra to this exchangeable σ-algebra: a tail event is fixed by every finitely supported
time permutation.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α β : Type*} [MeasurableSpace α]

/-- The exchangeable σ-algebra on path space: ambient-measurable events invariant under every
finitely supported permutation of the time coordinate. -/
@[implicit_reducible]
def exchangeableSigma (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  ⨅ π : {π : Equiv.Perm ℕ // (MulAction.fixedBy ℕ π)ᶜ.Finite},
    MeasurableSpace.invariants (permReindex (α := α) π.1)

/-- A set is measurable for `exchangeableSigma` iff it is ambient-measurable and fixed by every
finitely supported time permutation. -/
@[simp]
theorem mem_exchangeableSigma_iff {s : Set (ℕ → α)} :
    MeasurableSet[exchangeableSigma α] s ↔
      MeasurableSet s ∧
        ∀ π : Equiv.Perm ℕ, (MulAction.fixedBy ℕ π)ᶜ.Finite →
          permReindex (α := α) π ⁻¹' s = s := by
  rw [exchangeableSigma, MeasurableSpace.measurableSet_iInf]
  constructor
  · intro hs
    refine ⟨?_, ?_⟩
    · exact (MeasurableSpace.invariants_le (permReindex (α := α) (1 : Equiv.Perm ℕ))) _
        (hs ⟨1, by simp⟩)
    · intro π hπ
      exact (MeasurableSpace.measurableSet_invariants.mp (hs ⟨π, hπ⟩)).2
  · rintro ⟨hs_meas, hs_inv⟩ π
    exact MeasurableSpace.measurableSet_invariants.mpr ⟨hs_meas, hs_inv π.1 π.2⟩

/-- The exchangeable σ-algebra is a sub-σ-algebra of the ambient path-space σ-algebra. -/
theorem exchangeableSigma_le :
    exchangeableSigma α ≤ (inferInstance : MeasurableSpace (ℕ → α)) := by
  intro s hs
  exact (mem_exchangeableSigma_iff.mp hs).1

/-- An `exchangeableSigma`-measurable set is ambient-measurable. -/
theorem MeasurableSet.ambient_of_exchangeableSigma {s : Set (ℕ → α)}
    (hs : MeasurableSet[exchangeableSigma α] s) : MeasurableSet s :=
  exchangeableSigma_le s hs

/-- An ambient-measurable event fixed by every finitely supported time permutation is measurable
for the exchangeable σ-algebra. -/
theorem measurableSet_exchangeableSigma_of_forall_permReindex {s : Set (ℕ → α)}
    (hs_meas : MeasurableSet s)
    (hs_inv : ∀ π : Equiv.Perm ℕ, (MulAction.fixedBy ℕ π)ᶜ.Finite →
      permReindex (α := α) π ⁻¹' s = s) :
    MeasurableSet[exchangeableSigma α] s :=
  mem_exchangeableSigma_iff.mpr ⟨hs_meas, hs_inv⟩

/-- An exchangeable event is fixed by any finitely supported time permutation. -/
@[simp]
theorem MeasurableSet.preimage_permReindex_eq_of_exchangeableSigma {s : Set (ℕ → α)}
    (hs : MeasurableSet[exchangeableSigma α] s) {π : Equiv.Perm ℕ}
    (hπ : (MulAction.fixedBy ℕ π)ᶜ.Finite) :
    permReindex (α := α) π ⁻¹' s = s :=
  (mem_exchangeableSigma_iff.mp hs).2 π hπ

/-- Reindexing by any permutation is measurable as an endomap of the exchangeable σ-algebra. -/
theorem measurable_permReindex_exchangeableSigma (π : Equiv.Perm ℕ) :
    @Measurable (ℕ → α) (ℕ → α) (exchangeableSigma α) (exchangeableSigma α)
      (permReindex (α := α) π) := by
  intro s hs
  refine mem_exchangeableSigma_iff.mpr ⟨?_, ?_⟩
  · exact (measurable_reindex π) (mem_exchangeableSigma_iff.mp hs).1
  · intro σ hσ
    ext x
    simp only [Set.mem_preimage]
    have hconj : (MulAction.fixedBy ℕ (π⁻¹ * σ * π))ᶜ.Finite :=
      TauCeti.finite_compl_fixedBy_conj hσ
    have hinv := MeasurableSet.preimage_permReindex_eq_of_exchangeableSigma
      (α := α) hs hconj
    have hx := Set.ext_iff.mp hinv (permReindex (α := α) π x)
    have hleft :
        permReindex (α := α) (π⁻¹ * σ * π) (permReindex (α := α) π x) =
          permReindex (α := α) π (permReindex (α := α) σ x) := by
      rw [permReindex_permReindex, permReindex_permReindex]
      simp [mul_assoc]
    simpa [Set.mem_preimage, hleft] using hx

/-- An ambient-measurable observable fixed by every finitely supported reindexing is measurable
with respect to the exchangeable σ-algebra. -/
theorem measurable_exchangeableSigma_of_comp_permReindex_eq [MeasurableSpace β]
    {g : (ℕ → α) → β} (hg : Measurable g)
    (hg_perm : ∀ π : Equiv.Perm ℕ, (MulAction.fixedBy ℕ π)ᶜ.Finite →
      g ∘ permReindex (α := α) π = g) :
    @Measurable (ℕ → α) β (exchangeableSigma α) inferInstance g := by
  intro s hs
  refine mem_exchangeableSigma_iff.mpr ⟨hg hs, ?_⟩
  intro π hπ
  ext x
  exact Set.ext_iff.mp (congrFun (congrArg Set.preimage (hg_perm π hπ)) s) x

/-- For a target with measurable singletons, a function measurable with respect to the
exchangeable σ-algebra is fixed by every finitely supported reindexing. -/
theorem comp_permReindex_eq_of_measurable_exchangeableSigma [MeasurableSpace β]
    [MeasurableSingletonClass β] {g : (ℕ → α) → β}
    (hg : @Measurable (ℕ → α) β (exchangeableSigma α) inferInstance g)
    {π : Equiv.Perm ℕ} (hπ : (MulAction.fixedBy ℕ π)ᶜ.Finite) :
    g ∘ permReindex (α := α) π = g := by
  exact MeasurableSpace.comp_eq_of_measurable_invariants
    (hg.mono (iInf_le (fun π : {π : Equiv.Perm ℕ //
      (MulAction.fixedBy ℕ π)ᶜ.Finite} =>
      MeasurableSpace.invariants (permReindex (α := α) π.1)) ⟨π, hπ⟩) le_rfl)

/-- If a set belongs to the future path σ-algebra from time `N` onward and `π` fixes every index
`k ≥ N`, then reindexing paths by `π` leaves the set fixed. -/
private theorem preimage_permReindex_eq_of_measurable_tailFamily
    {s : Set (ℕ → α)} {π : Equiv.Perm ℕ} {N : ℕ}
    (hs : MeasurableSet[tailFamily (fun k (x : ℕ → α) => x k) N] s)
    (hπ : ∀ k, N ≤ k → π k = k) :
    permReindex (α := α) π ⁻¹' s = s := by
  rw [tailFamily_eq_iSup_comap] at hs
  rw [MeasurableSpace.measurableSet_iSup] at hs
  induction hs with
  | basic u hu =>
      rcases hu with ⟨k, t, ht, rfl⟩
      ext x
      simp only [Set.mem_preimage]
      rw [permReindex_apply, hπ k.1 k.2]
  | empty =>
      simp
  | compl t ht hpre =>
      rw [Set.preimage_compl, hpre]
  | iUnion f _ hf =>
      rw [Set.preimage_iUnion]
      simp [hf]

/-- The path-space tail σ-algebra is contained in the exchangeable σ-algebra: tail events are
fixed by every finitely supported permutation of the time coordinate. -/
theorem pathTail_le_exchangeableSigma :
    pathTail α ≤ exchangeableSigma α := by
  intro s hs
  refine mem_exchangeableSigma_iff.mpr ⟨?_, ?_⟩
  · exact tailProcess_le_ambient 0 (X := fun k (x : ℕ → α) => x k)
      (fun k _ => measurable_pi_apply k) s hs
  · intro π hπ
    rcases TauCeti.finite_compl_fixedBy_eventually_eq_self hπ with ⟨N, hN⟩
    exact preimage_permReindex_eq_of_measurable_tailFamily
      ((pathTail_le_tailFamily (α := α) N) s hs) hN

/-- The path-space tail σ-algebra is contained in the exchangeable σ-algebra. -/
theorem tail_le_exchangeableSigma :
    pathTail α ≤ exchangeableSigma α :=
  pathTail_le_exchangeableSigma

end Probability

end TauCeti
