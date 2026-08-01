/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Logic.Embedding.Set
import Mathlib.Algebra.Group.Pointwise.Set.Finite

/-!
# Finitely supported permutations

This file records small bridges for Mathlib's finite-support predicate for permutations,
`(MulAction.fixedBy ι π)ᶜ.Finite`.
-/

public section

namespace TauCeti

/-- Constructor for Mathlib's finite-support predicate from an eventual fixedness bound. -/
theorem finite_compl_fixedBy_of_eventually_eq_self {π : Equiv.Perm ℕ}
    (hπ : ∃ N, ∀ n, N ≤ n → π n = n) : (MulAction.fixedBy ℕ π)ᶜ.Finite := by
  rcases hπ with ⟨N, hN⟩
  exact (Set.finite_Iio N).subset fun n hn => by
    by_contra hnN
    have hfixed : n ∈ MulAction.fixedBy ℕ π := by
      simpa [MulAction.mem_fixedBy, Equiv.Perm.smul_def] using hN n (not_lt.mp hnN)
    exact hn hfixed

/-- A permutation of `ℕ` with finite Mathlib support fixes every sufficiently large index. -/
theorem finite_compl_fixedBy_eventually_eq_self {π : Equiv.Perm ℕ}
    (hπ : (MulAction.fixedBy ℕ π)ᶜ.Finite) : ∃ N, ∀ n, N ≤ n → π n = n := by
  rcases hπ.bddAbove with ⟨N, hN⟩
  refine ⟨N + 1, fun n hn => ?_⟩
  by_contra hne
  have hn_support : n ∈ (MulAction.fixedBy ℕ π)ᶜ := by
    simpa [MulAction.mem_fixedBy, Equiv.Perm.smul_def] using hne
  exact (not_lt_of_ge hn) (Nat.lt_succ_of_le (hN hn_support))

/-- A permutation of `ℕ` is finitely supported iff it fixes all sufficiently large indices. -/
theorem finite_compl_fixedBy_iff_eventually_eq_self {π : Equiv.Perm ℕ} :
    (MulAction.fixedBy ℕ π)ᶜ.Finite ↔ ∃ N, ∀ n, N ≤ n → π n = n :=
  ⟨finite_compl_fixedBy_eventually_eq_self, finite_compl_fixedBy_of_eventually_eq_self⟩

/-- Conjugating a group element preserves Mathlib's finite-support predicate
`(MulAction.fixedBy α ·)ᶜ.Finite`; in particular this applies to conjugation of permutations. -/
theorem finite_compl_fixedBy_conj {G α : Type*} [Group G] [MulAction G α] {g h : G}
    (hh : (MulAction.fixedBy α h)ᶜ.Finite) : (MulAction.fixedBy α (g⁻¹ * h * g))ᶜ.Finite := by
  simpa [Set.smul_set_compl, MulAction.smul_fixedBy] using hh.smul_set (a := g⁻¹)

end TauCeti

namespace Equiv.Perm

/-- **A pair of embeddings from a finite type is realised by a permutation supported on their
ranges.** For `f g : ι ↪ β` with `ι` finite there is a permutation of `β` carrying each `f i` to
`g i` and fixing every point outside `Set.range f ∪ Set.range g`.

That union is finite, so `Set.Finite.subset` turns the containment into finite support in the sense
of `(MulAction.fixedBy β σ)ᶜ.Finite`. -/
theorem exists_compl_fixedBy_subset_apply_eq {ι β : Type*} [Finite ι] (f g : ι ↪ β) :
    ∃ σ : Equiv.Perm β,
      (MulAction.fixedBy β σ)ᶜ ⊆ Set.range f ∪ Set.range g ∧ ∀ i, σ (f i) = g i := by
  classical
  set T : Set β := Set.range f ∪ Set.range g with hT
  haveI : Fintype ↥T := ((Set.finite_range f).union (Set.finite_range g)).fintype
  have hfT : ∀ i, f i ∈ T := fun i => Or.inl ⟨i, rfl⟩
  have hgT : ∀ i, g i ∈ T := fun i => Or.inr ⟨i, rfl⟩
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (f.codRestrict T hfT) (g.codRestrict T hgT)
    (f.codRestrict T hfT).injective (g.codRestrict T hgT).injective
  refine ⟨Equiv.Perm.viaFintypeEmbedding σ (Function.Embedding.subtype _), fun b hb => ?_,
    fun i => ?_⟩
  · by_contra hbT
    refine hb ?_
    simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
    refine Equiv.Perm.viaFintypeEmbedding_apply_notMem_range σ _ ?_
    rintro ⟨x, rfl⟩
    exact hbT x.2
  · calc (Equiv.Perm.viaFintypeEmbedding σ (Function.Embedding.subtype _)) (f i)
        = ((σ (f.codRestrict T hfT i) : ↥T) : β) :=
          Equiv.Perm.viaFintypeEmbedding_apply_image σ _ (f.codRestrict T hfT i)
      _ = g i := congrArg Subtype.val (hσ i)

/-- Finite-support form of `Equiv.Perm.exists_compl_fixedBy_subset_apply_eq`: for `f g : ι ↪ β`
with `ι` finite there is a permutation of `β` carrying each `f i` to `g i` whose support is finite.

This is the shape consumers of finitely supported reindexing want, `(MulAction.fixedBy β σ)ᶜ.Finite`
being Mathlib's finite-support predicate. -/
theorem exists_finite_compl_fixedBy_apply_eq {ι β : Type*} [Finite ι] (f g : ι ↪ β) :
    ∃ σ : Equiv.Perm β, (MulAction.fixedBy β σ)ᶜ.Finite ∧ ∀ i, σ (f i) = g i := by
  obtain ⟨σ, hsub, hval⟩ := exists_compl_fixedBy_subset_apply_eq f g
  exact ⟨σ, ((Set.finite_range f).union (Set.finite_range g)).subset hsub, hval⟩

end Equiv.Perm
