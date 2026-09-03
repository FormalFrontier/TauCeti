/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Filter
public import TauCeti.Data.Sym.Basic
import Mathlib.Data.List.FinRange

/-!
# Tuples mapped into pairwise disjoint ranges

An ordered tuple mapped pointwise into pairwise disjoint ranges is determined by the unordered
tuple it presents. This file proves that injectivity statement and characterizes the range by
counting how many points lie in each component range. The corresponding topological open embedding
is in `TauCeti/Topology/Sym/Disjoint.lean`.

## Main declarations

* `TauCeti.Sym.ofFn_map_injective`: ordered tuples mapped into pairwise disjoint ranges are
  determined by the unordered tuples they present, with `TauCeti.Sym.mem_range_ofFn_map`
  describing those unordered tuples.
-/

public section

namespace TauCeti

namespace Sym

variable {α : Type*} {n : ℕ}

/-! ### Tuples mapped into pairwise disjoint ranges -/

/-- An ordered tuple mapped pointwise into pairwise disjoint ranges is determined by the unordered
tuple it presents. A permutation matching two such tuples must fix every index. -/
theorem ofFn_map_injective {X : Fin n → Type*} (f : ∀ i, X i → α)
    (hf : ∀ i, Function.Injective (f i))
    (h : Pairwise (Function.onFun Disjoint fun i => Set.range (f i))) :
    Function.Injective fun x : ∀ i, X i => ofFn fun i => f i (x i) := by
  intro x y hxy
  obtain ⟨σ, hσ⟩ := ofFn_eq_ofFn_iff.1 hxy
  have hval : ∀ i, f (σ i) (x (σ i)) = f i (y i) := fun i => congrFun hσ i
  have hfix : ∀ i, σ i = i := fun i => by
    by_contra hne
    exact Set.disjoint_left.1 (h hne) (Set.mem_range_self (x (σ i)))
      ⟨y i, (hval i).symm⟩
  exact funext fun i => hf i <|
    (congrArg (fun j => f j (x j)) (hfix i)).symm.trans (hval i)

attribute [local instance] Classical.propDecidable

/-- The range of ordered tuples mapped pointwise into pairwise disjoint ranges consists exactly of
the unordered tuples having one point in each range. -/
theorem mem_range_ofFn_map {X : Fin n → Type*} (f : ∀ i, X i → α)
    (h : Pairwise (Function.onFun Disjoint fun i => Set.range (f i))) {w : Sym α n} :
    w ∈ Set.range (fun x : ∀ i, X i => ofFn fun i => f i (x i)) ↔
      ∀ i, Multiset.card
        (Multiset.filter (· ∈ Set.range (f i)) (w : Multiset α)) = 1 := by
  classical
  constructor
  · rintro ⟨x, rfl⟩ i
    set a : Fin n → α := fun j => f j (x j)
    have ha : Function.Injective a := by
      intro j k hjk
      by_contra hne
      exact Set.disjoint_left.1 (h hne) (Set.mem_range_self (x j))
        ⟨x k, hjk.symm⟩
    have hnodup : (ofFn a : Multiset α).Nodup := by
      rw [coe_ofFn]
      exact List.nodup_ofFn.2 ha
    have hfilter : Multiset.filter (· ∈ Set.range (f i)) (ofFn a : Multiset α) = {a i} := by
      apply (Multiset.Nodup.ext (hnodup.filter _) (Multiset.nodup_singleton _)).2
      intro b
      rw [Multiset.mem_filter, Multiset.mem_singleton]
      constructor
      · rintro ⟨hb, hbi⟩
        obtain ⟨j, hj⟩ := mem_ofFn.1 (_root_.Sym.mem_coe.1 hb)
        have hji : j = i := by
          by_contra hne
          exact Set.disjoint_left.1 (h hne) ⟨x j, hj⟩ hbi
        simpa [hji] using hj.symm
      · rintro rfl
        exact ⟨_root_.Sym.mem_coe.2 (mem_ofFn.2 ⟨i, rfl⟩), Set.mem_range_self (x i)⟩
    rw [hfilter]
    simp
  · intro hcount
    have hex : ∀ i, ∃ a, a ∈ w ∧ a ∈ Set.range (f i) := by
      intro i
      have hpos : 0 < Multiset.card
          (Multiset.filter (· ∈ Set.range (f i)) (w : Multiset α)) := by
        rw [hcount i]
        exact Nat.zero_lt_succ 0
      obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
      exact ⟨a, (_root_.Sym.mem_coe.1 (Multiset.mem_filter.1 ha).1),
        (Multiset.mem_filter.1 ha).2⟩
    choose a ha using hex
    have haw : ∀ i, a i ∈ w := fun i => (ha i).1
    have har : ∀ i, a i ∈ Set.range (f i) := fun i => (ha i).2
    have hainj : Function.Injective a := by
      intro i j hij
      by_contra hne
      exact Set.disjoint_left.1 (h hne) (har i) (hij.symm ▸ har j)
    choose x hx using har
    have hnodup : (↑(List.ofFn a) : Multiset α).Nodup := List.nodup_ofFn.2 hainj
    have hle : (↑(List.ofFn a) : Multiset α) ≤ (w : Multiset α) :=
      (Multiset.le_iff_subset hnodup).2 fun b hb => by
        rw [← coe_ofFn] at hb
        obtain ⟨i, hi⟩ := mem_ofFn.1 (_root_.Sym.mem_coe.1 hb)
        exact _root_.Sym.mem_coe.2 (hi ▸ haw i)
    have heq : (↑(List.ofFn a) : Multiset α) = (w : Multiset α) :=
      Multiset.eq_of_le_of_card_le hle (by simp)
    have hofa : ofFn a = w := Sym.coe_injective (by simpa using heq)
    refine ⟨x, ?_⟩
    exact (congrArg ofFn (funext hx)).trans hofa

end Sym

end TauCeti
