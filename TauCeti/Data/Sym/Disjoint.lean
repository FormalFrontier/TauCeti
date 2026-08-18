/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Filter
public import TauCeti.Data.Sym.Basic

/-!
# Splitting an unordered tuple along two disjoint sets

An unordered `(n + m)`-tuple of points of `α` all of whose points lie in `U ∪ V`, with `U` and `V`
disjoint, is the same thing as a pair consisting of an unordered `n`-tuple of points of `U` and an
unordered `m`-tuple of points of `V`: the two parts are recovered from the tuple by filtering on
membership in `U`. This file constructs the map `TauCeti.Sym.appendSubtype` in one direction and
proves that it is injective with the expected range.

Nothing here is topological. `TauCeti/Topology/Sym/Disjoint.lean` upgrades the same map to an open
embedding when `U` and `V` are open, which is what presents a symmetric power as a product of
smaller symmetric powers near a tuple with repeated points.

## Main declarations

* `TauCeti.Sym.appendSubtype`: an unordered `n`-tuple of points of `U` and an unordered `m`-tuple
  of points of `V`, concatenated into an unordered `(n + m)`-tuple of points of `α`, with
  `TauCeti.Sym.appendSubtype_ofFn` and `TauCeti.Sym.appendSubtype_comp_ofFn` reading it on
  ordered tuples.
* `TauCeti.Sym.appendSubtype_injective`: for disjoint `U` and `V` the concatenation determines
  both of its parts.
* `TauCeti.Sym.mem_range_appendSubtype`: its range consists of the tuples supported in `U ∪ V`
  with exactly `n` points in `U`.
* `TauCeti.Sym.ofFn_val_injective`: the ordered tuples with `i`-th point in `U i`, for a pairwise
  disjoint family `U`, are determined by the unordered tuples they present.
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

/-- Concatenating the unordered tuples presented by two ordered ones is the unordered tuple
presented by their concatenation `Fin.append`. -/
@[simp]
theorem appendSubtype_ofFn (f : Fin n → U) (g : Fin m → V) :
    appendSubtype U V n m (ofFn f, ofFn g) =
      ofFn (Fin.append (fun i => (f i : α)) fun j => (g j : α)) := by
  simp [appendSubtype, Function.comp_def]

/-- The same statement as `TauCeti.Sym.appendSubtype_ofFn` read as an equality of maps out of the
pairs of ordered tuples, which is the form the quotient topology consumes. -/
theorem appendSubtype_comp_ofFn :
    appendSubtype U V n m ∘ Prod.map ofFn ofFn =
      ofFn ∘ (fun q : (Fin n → α) × (Fin m → α) => Fin.append q.1 q.2) ∘
        Prod.map (Pi.map fun _ : Fin n => (Subtype.val : U → α))
          (Pi.map fun _ : Fin m => (Subtype.val : V → α)) := by
  funext p
  obtain ⟨f, g⟩ := p
  simp only [Function.comp_apply, Prod.map_apply, appendSubtype_ofFn, ofFn_fin_append]
  rfl

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
theorem filter_mem_map_val_add [DecidablePred (· ∈ U)] (h : Disjoint U V) (s : Multiset U)
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
  refine ⟨(⟨A.attach.map fun x => ⟨x.1, hAU x.1 x.2⟩, ?_⟩,
    ⟨B.attach.map fun x => ⟨x.1, hBV x.1 x.2⟩, ?_⟩), Sym.coe_injective ?_⟩
  · simpa using hA
  · simpa using hB
  · simpa [Multiset.map_map, Function.comp_def, Multiset.attach_map_val] using hAB

/-- The range of concatenation along a disjoint pair of sets: the unordered tuples supported in
`U ∪ V` with exactly `n` of their points in `U`. -/
theorem mem_range_appendSubtype [DecidablePred (· ∈ U)] (h : Disjoint U V) {w : Sym α (n + m)} :
    w ∈ Set.range (appendSubtype U V n m) ↔
      (∀ a ∈ w, a ∈ U ∪ V) ∧
        Multiset.card (Multiset.filter (· ∈ U) (w : Multiset α)) = n := by
  refine ⟨?_, fun hw => exists_appendSubtype_eq hw.1 hw.2⟩
  rintro ⟨p, rfl⟩
  exact ⟨fun a ha => mem_union_of_mem_appendSubtype ha, card_filter_mem_appendSubtype h p⟩

/-! ### Tuples with one point in each of pairwise disjoint sets -/

/-- An ordered tuple whose `i`-th point lies in `U i`, for a pairwise disjoint family `U`, is
determined by the unordered tuple it presents: a permutation matching the two tuples must fix every
index, since disjoint sets share no point. -/
theorem ofFn_val_injective {U : Fin n → Set α} (h : Pairwise (Function.onFun Disjoint U)) :
    Function.Injective fun f : (i : Fin n) → U i => ofFn fun i => (f i : α) := by
  intro f g hfg
  obtain ⟨σ, hσ⟩ := ofFn_eq_ofFn_iff.1 hfg
  have hval : ∀ i, (f (σ i) : α) = (g i : α) := fun i => congrFun hσ i
  have hfix : ∀ i, σ i = i := fun i => by
    by_contra hne
    exact Set.disjoint_left.1 (h hne) (hval i ▸ (f (σ i)).2) (g i).2
  exact funext fun i => Subtype.ext (by rw [← hval i, hfix i])

end Sym

end TauCeti
