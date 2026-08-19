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
# Splitting an unordered tuple along two disjoint sets

An unordered `(n + m)`-tuple of points of `α` all of whose points lie in `U ∪ V`, with exactly `n`
of them in `U` and with `U` and `V` disjoint, is the same thing as a pair consisting of an unordered
`n`-tuple of points of `U` and an unordered `m`-tuple of points of `V`: the two parts are recovered
from the tuple by filtering on membership in `U`. This file constructs the map
`TauCeti.Sym.appendSubtype` in one direction and proves that it is injective with the expected
range.

Nothing here is topological. `TauCeti/Topology/Sym/Disjoint.lean` upgrades the same map to an open
embedding when `U` and `V` are open, which is what presents a symmetric power as a product of
smaller symmetric powers near a tuple with repeated points.

## Main declarations

* `TauCeti.Sym.appendSubtype`: an unordered `n`-tuple of points of `U` and an unordered `m`-tuple
  of points of `V`, concatenated into an unordered `(n + m)`-tuple of points of `α`, with
  `TauCeti.Sym.appendSubtype_ofFn` reading it on ordered tuples.
* `TauCeti.Sym.appendSubtype_injective`: for disjoint `U` and `V` the concatenation determines
  both of its parts.
* `TauCeti.Sym.mem_range_appendSubtype`: its range consists of the tuples supported in `U ∪ V`
  with exactly `n` points in `U`.
* `TauCeti.Sym.ofFn_map_injective`: ordered tuples mapped into pairwise disjoint ranges are
  determined by the unordered tuples they present, with `TauCeti.Sym.mem_range_ofFn_map`
  describing those unordered tuples.
-/

public section

namespace TauCeti

namespace Sym

variable {α : Type*} {m n : ℕ} {U V : Set α}

/-! ### Concatenation along a disjoint pair of sets -/

/-- The concatenation of an unordered `n`-tuple of points of `U` and an unordered `m`-tuple of
points of `V`, read as an unordered `(n + m)`-tuple of points of `α`. -/
def appendSubtype (U V : Set α) (n m : ℕ) (p : Sym U n × Sym V m) : Sym α (n + m) :=
  (Sym.map Subtype.val p.1).append (Sym.map Subtype.val p.2)

@[simp]
theorem coe_appendSubtype (p : Sym U n × Sym V m) :
    (appendSubtype U V n m p : Multiset α) =
      (p.1 : Multiset U).map Subtype.val + (p.2 : Multiset V).map Subtype.val := by
  simp [appendSubtype, Sym.coe_append, Sym.coe_map]

/-- Concatenation along subtypes factors through the two maps on symmetric powers followed by
ordinary concatenation. -/
theorem appendSubtype_eq_append_map :
    appendSubtype U V n m = (fun p : Sym α n × Sym α m => p.1.append p.2) ∘
      Prod.map (Sym.map (Subtype.val : U → α)) (Sym.map (Subtype.val : V → α)) := by
  funext p
  exact Sym.coe_injective (by simp [coe_appendSubtype, Sym.coe_append, Sym.coe_map])

/-- Concatenating the unordered tuples presented by two ordered ones is the unordered tuple
presented by their concatenation `Fin.append`. -/
@[simp]
theorem appendSubtype_ofFn (f : Fin n → U) (g : Fin m → V) :
    appendSubtype U V n m (ofFn f, ofFn g) =
      ofFn (Fin.append (fun i => (f i : α)) fun j => (g j : α)) := by
  simp [appendSubtype, Function.comp_def]

/-- Every point of a concatenated tuple lies in one of the two sets. -/
theorem mem_union_of_mem_appendSubtype {a : α} {p : Sym U n × Sym V m}
    (ha : a ∈ appendSubtype U V n m p) : a ∈ U ∪ V := by
  rw [← Sym.mem_coe, coe_appendSubtype, Multiset.mem_add] at ha
  obtain h | h := ha
  · obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 h
    exact Or.inl x.2
  · obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 h
    exact Or.inr y.2

/-- Filtering a concatenation on membership in `U` recovers its first part, the second part
contributing nothing because it is supported in the disjoint set `V`. -/
private theorem filter_mem_map_val_add [DecidablePred (· ∈ U)] (h : Disjoint U V)
    (s : Multiset U)
    (t : Multiset V) :
    Multiset.filter (· ∈ U) (s.map Subtype.val + t.map Subtype.val) = s.map Subtype.val := by
  have hs : Multiset.filter (· ∈ U) (s.map Subtype.val) = s.map Subtype.val :=
    Multiset.filter_eq_self.2 fun a ha => by
      obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 ha
      exact x.2
  have ht : Multiset.filter (· ∈ U) (t.map Subtype.val) = 0 :=
    Multiset.filter_eq_nil.2 fun a ha => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 ha
      exact Set.disjoint_right.1 h y.2
  rw [Multiset.filter_add, hs, ht, add_zero]

/-- A concatenation has exactly `n` points in `U`. -/
theorem card_filter_mem_appendSubtype [DecidablePred (· ∈ U)] (h : Disjoint U V)
    (p : Sym U n × Sym V m) :
    Multiset.card (Multiset.filter (· ∈ U) (appendSubtype U V n m p : Multiset α)) = n := by
  rw [coe_appendSubtype, filter_mem_map_val_add h, Multiset.card_map]
  exact p.1.2

/-- Concatenation along a disjoint pair of sets is injective: the two parts of the tuple are
recovered by filtering on membership in `U`. -/
theorem appendSubtype_injective (h : Disjoint U V) :
    Function.Injective (appendSubtype U V n m) := by
  classical
  rintro ⟨s, t⟩ ⟨s', t'⟩ hp
  have hcoe : (s : Multiset U).map Subtype.val + (t : Multiset V).map Subtype.val =
      (s' : Multiset U).map Subtype.val + (t' : Multiset V).map Subtype.val := by
    simpa using congrArg (fun w : Sym α (n + m) => (w : Multiset α)) hp
  have hfst : (s : Multiset U).map Subtype.val = (s' : Multiset U).map Subtype.val := by
    have := congrArg (Multiset.filter (· ∈ U)) hcoe
    rwa [filter_mem_map_val_add h, filter_mem_map_val_add h] at this
  have hsnd : (t : Multiset V).map Subtype.val = (t' : Multiset V).map Subtype.val := by
    rw [hfst] at hcoe
    exact add_left_cancel hcoe
  exact Prod.ext (Sym.coe_injective (Multiset.map_injective Subtype.val_injective hfst))
    (Sym.coe_injective (Multiset.map_injective Subtype.val_injective hsnd))

/-- A tuple supported in `U ∪ V` with exactly `n` of its points in `U` is a concatenation.
Disjointness is not needed here; it is what makes the two parts unique. -/
theorem exists_appendSubtype_eq [DecidablePred (· ∈ U)] {w : Sym α (n + m)}
    (hw : ∀ a ∈ w, a ∈ U ∪ V)
    (hn : Multiset.card (Multiset.filter (· ∈ U) (w : Multiset α)) = n) :
    ∃ p, appendSubtype U V n m p = w := by
  obtain ⟨A, B, hAB, hAU, hBV, hA⟩ :
      ∃ A B : Multiset α, A + B = (w : Multiset α) ∧ (∀ a ∈ A, a ∈ U) ∧ (∀ a ∈ B, a ∈ V) ∧
        Multiset.card A = n := by
    refine ⟨Multiset.filter (· ∈ U) (w : Multiset α),
      Multiset.filter (fun a => ¬ a ∈ U) (w : Multiset α), Multiset.filter_add_not _ _,
      fun a ha => (Multiset.mem_filter.1 ha).2, fun a ha => ?_, hn⟩
    obtain ⟨hmem, hnot⟩ := Multiset.mem_filter.1 ha
    exact (hw a hmem).resolve_left hnot
  have hB : Multiset.card B = m := by
    have hcard : Multiset.card A + Multiset.card B = n + m := by
      rw [← Multiset.card_add, hAB]
      exact w.2
    omega
  have hArange : (⟨A, hA⟩ : Sym α n) ∈ Set.range (Sym.map (Subtype.val : U → α)) :=
    (mem_range_map Subtype.val).2 fun a ha =>
      ⟨⟨a, hAU a (_root_.Sym.mem_coe.2 ha)⟩, rfl⟩
  have hBrange : (⟨B, hB⟩ : Sym α m) ∈ Set.range (Sym.map (Subtype.val : V → α)) :=
    (mem_range_map Subtype.val).2 fun a ha =>
      ⟨⟨a, hBV a (_root_.Sym.mem_coe.2 ha)⟩, rfl⟩
  obtain ⟨s, hs⟩ := hArange
  obtain ⟨t, ht⟩ := hBrange
  refine ⟨(s, t), Sym.coe_injective ?_⟩
  rw [coe_appendSubtype]
  have hs' : (s : Multiset U).map Subtype.val = A := by
    simpa [Sym.coe_map] using congrArg (fun z : Sym α n => (z : Multiset α)) hs
  have ht' : (t : Multiset V).map Subtype.val = B := by
    simpa [Sym.coe_map] using congrArg (fun z : Sym α m => (z : Multiset α)) ht
  rw [hs', ht', hAB]

/-- The range of concatenation along a disjoint pair of sets: the unordered tuples supported in
`U ∪ V` with exactly `n` of their points in `U`. -/
theorem mem_range_appendSubtype [DecidablePred (· ∈ U)] (h : Disjoint U V) {w : Sym α (n + m)} :
    w ∈ Set.range (appendSubtype U V n m) ↔
      (∀ a ∈ w, a ∈ U ∪ V) ∧
        Multiset.card (Multiset.filter (· ∈ U) (w : Multiset α)) = n := by
  refine ⟨?_, fun hw => exists_appendSubtype_eq hw.1 hw.2⟩
  rintro ⟨p, rfl⟩
  exact ⟨fun a ha => mem_union_of_mem_appendSubtype ha, card_filter_mem_appendSubtype h p⟩

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
