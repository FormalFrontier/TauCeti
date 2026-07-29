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
    (hh : (MulAction.fixedBy α h)ᶜ.Finite) :
    (MulAction.fixedBy α (g⁻¹ * h * g))ᶜ.Finite := by
  simpa [Set.smul_set_compl, MulAction.smul_fixedBy] using hh.smul_set (a := g⁻¹)

/-- **A pair of embeddings from a finite type is realised by a finitely supported permutation.**
For `f g : ι ↪ β` with `ι` finite there is a permutation of `β` carrying each `f i` to `g i` and
fixing everything outside the finite set `range f ∪ range g`.

Mathlib's `Equiv.Perm.exists_extending_pair` already supplies a permutation with the right values,
but it matches the complements of the ranges by an arbitrary bijection, so it need not be finitely
supported. Applying it inside the finite subtype `range f ∪ range g` and pushing the result out with
`Equiv.Perm.viaFintypeEmbedding` keeps it the identity off that set. -/
theorem exists_finiteSupport_perm_apply_eq {ι β : Type*} [Finite ι] (f g : ι ↪ β) :
    ∃ σ : Equiv.Perm β, (MulAction.fixedBy β σ)ᶜ.Finite ∧ ∀ i, σ (f i) = g i := by
  classical
  set T : Set β := Set.range f ∪ Set.range g with hT
  have hTfin : T.Finite := (Set.finite_range f).union (Set.finite_range g)
  haveI : Fintype ↥T := hTfin.fintype
  have hfT : ∀ i, f i ∈ T := fun i => Or.inl ⟨i, rfl⟩
  have hgT : ∀ i, g i ∈ T := fun i => Or.inr ⟨i, rfl⟩
  have hf' : Function.Injective (fun i => (⟨f i, hfT i⟩ : ↥T)) := fun a b h =>
    f.injective (congrArg Subtype.val h)
  have hg' : Function.Injective (fun i => (⟨g i, hgT i⟩ : ↥T)) := fun a b h =>
    g.injective (congrArg Subtype.val h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hf' hg'
  set emb : ↥T ↪ β := ⟨Subtype.val, Subtype.val_injective⟩ with hemb
  refine ⟨Equiv.Perm.viaFintypeEmbedding σ emb, hTfin.subset fun b hb => ?_, fun i => ?_⟩
  · by_contra hbT
    refine hb ?_
    simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
    refine Equiv.Perm.viaFintypeEmbedding_apply_notMem_range σ emb ?_
    rintro ⟨x, rfl⟩
    exact hbT x.2
  · calc (Equiv.Perm.viaFintypeEmbedding σ emb) (f i)
        = ((σ ⟨f i, hfT i⟩ : ↥T) : β) :=
          Equiv.Perm.viaFintypeEmbedding_apply_image σ emb ⟨f i, hfT i⟩
      _ = g i := congrArg Subtype.val (hσ i)

end TauCeti
