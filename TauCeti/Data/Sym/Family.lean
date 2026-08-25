/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Multiset.Filter
public import TauCeti.Data.Sym.Basic

/-!
# Splitting an unordered tuple along a pairwise disjoint family of sets

This file concatenates unordered tuples along a finite family `U : ι → Set α` of pairwise disjoint
sets: a family of
unordered tuples, the `i`-th of them an `m i`-tuple of points of `U i`, concatenates into an
unordered `n`-tuple of points of `α` as soon as `∑ i, m i = n`, and the parts are recovered from the
whole by filtering on membership in `U i`.

Nothing here is topological. `TauCeti/Topology/Sym/Family.lean` upgrades the concatenation to an
open embedding when the `U i` are open, and shows that in a Hausdorff space every unordered tuple
lies in the range of such a concatenation, with one member of the family for each of its distinct
points and that point's multiplicity as the degree. That is the decomposition which charts the
symmetric power of a surface near a tuple with repeated points.

Because the degrees are required to add up to a *given* `n` rather than the target degree being
literally `∑ i, m i`, the concatenation composes with other maps of symmetric powers without a
cast.

## Main declarations

* `TauCeti.Sym.sumSubtype`: the concatenation of a family of unordered tuples of points of the
  members of the family, as an unordered `n`-tuple of points of `α`.
* `TauCeti.Sym.filter_mem_sumSubtype` and `TauCeti.Sym.sumSubtype_injective`: for a pairwise
  disjoint family the concatenation determines all of its parts.
* `TauCeti.Sym.mem_range_sumSubtype`: its range consists of the tuples supported in the union of
  the family with exactly `m i` of their points in `U i`.
* `TauCeti.Sym.sumSubtype_ofFn`: the concatenation read on ordered tuples, along a bijection
  `(Σ i, Fin (m i)) ≃ Fin n`.
-/

public section

namespace TauCeti

namespace Sym

variable {α ι : Type*} [Fintype ι] {U : ι → Set α} {m : ι → ℕ} {n : ℕ}

/-! ### Ordered tuples and multiplicities -/

/-- A sigma type of finite sets whose cardinalities add up to `n` is equivalent to `Fin n`. -/
theorem nonempty_sigmaFinEquiv (hn : ∑ i, m i = n) :
    Nonempty ((Σ i, Fin (m i)) ≃ Fin n) :=
  ⟨Fintype.equivFinOfCardEq (by simpa using hn)⟩

/-- The multiset underlying an ordered tuple, as a sum of singletons. This is the shape in which
`TauCeti.Sym.ofFn` meets the sum of multisets defining `TauCeti.Sym.sumSubtype`. -/
private theorem coe_ofFn_eq_sum {β : Type*} {k : ℕ} (g : Fin k → β) :
    (ofFn g : Multiset β) = ∑ j, ({g j} : Multiset β) := by
  have hmap : (ofFn g : Multiset β) = Multiset.map g (Finset.univ : Finset (Fin k)).val := by
    rw [coe_ofFn, Fin.univ_val_map]
  rw [hmap, ← Finset.sum_multiset_singleton (Finset.univ : Finset (Fin k)),
    ← Multiset.coe_mapAddMonoidHom g, map_sum]
  simp

/-! ### Concatenation along a pairwise disjoint family -/

/-- The concatenation of a family of unordered tuples, the `i`-th of them an unordered `m i`-tuple
of points of `U i`, read as an unordered `n`-tuple of points of `α`, the degrees being required to
add up to `n`.

This is the family used to chart a symmetric power near a tuple with repeated points: one member
for each distinct point of the tuple, with its multiplicity as the degree. -/
def sumSubtype (U : ι → Set α) (m : ι → ℕ) (hn : ∑ i, m i = n) (p : ∀ i, Sym (U i) (m i)) :
    Sym α n :=
  ⟨∑ i, (p i : Multiset (U i)).map Subtype.val, by
    simp only [Multiset.card_sum, Multiset.card_map]
    rw [← hn]
    exact Finset.sum_congr rfl fun i _ => (p i).2⟩

@[simp]
theorem coe_sumSubtype (hn : ∑ i, m i = n) (p : ∀ i, Sym (U i) (m i)) :
    (sumSubtype U m hn p : Multiset α) = ∑ i, (p i : Multiset (U i)).map Subtype.val :=
  (rfl)

/-- Every point of a concatenated tuple lies in one of the sets of the family. -/
theorem exists_mem_of_mem_sumSubtype {a : α} {hn : ∑ i, m i = n} {p : ∀ i, Sym (U i) (m i)}
    (ha : a ∈ sumSubtype U m hn p) : ∃ i, a ∈ U i := by
  rw [← _root_.Sym.mem_coe, coe_sumSubtype, Multiset.mem_sum] at ha
  obtain ⟨i, -, hi⟩ := ha
  obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hi
  exact ⟨i, x.2⟩

omit [Fintype ι] in
/-- Filtering distributes over a finite sum of multisets. -/
private theorem filter_finsetSum (q : α → Prop) [DecidablePred q] (s : Finset ι)
    (f : ι → Multiset α) :
    Multiset.filter q (∑ i ∈ s, f i) = ∑ i ∈ s, Multiset.filter q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, Multiset.filter_add, ih, Finset.sum_insert ha]

/-- Filtering a concatenation on membership in `U i` recovers its `i`-th part: the other parts
contribute nothing, being supported in sets disjoint from `U i`. -/
theorem filter_mem_sumSubtype [∀ i, DecidablePred (· ∈ U i)]
    (h : Pairwise (Function.onFun Disjoint U)) (hn : ∑ i, m i = n) (p : ∀ i, Sym (U i) (m i))
    (i : ι) :
    Multiset.filter (· ∈ U i) (sumSubtype U m hn p : Multiset α)
      = (p i : Multiset (U i)).map Subtype.val := by
  have hself : Multiset.filter (· ∈ U i) ((p i : Multiset (U i)).map Subtype.val)
      = (p i : Multiset (U i)).map Subtype.val :=
    Multiset.filter_eq_self.2 fun a ha => by
      obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 ha
      exact x.2
  rw [coe_sumSubtype, filter_finsetSum, Finset.sum_eq_single i, hself]
  · refine fun j _ hj => Multiset.filter_eq_nil.2 fun a ha => ?_
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 ha
    exact Set.disjoint_left.1 (h hj) x.2
  · exact fun hi => absurd (Finset.mem_univ i) hi

/-- A concatenation has exactly `m i` points in `U i`. -/
theorem card_filter_mem_sumSubtype [∀ i, DecidablePred (· ∈ U i)]
    (h : Pairwise (Function.onFun Disjoint U)) (hn : ∑ i, m i = n) (p : ∀ i, Sym (U i) (m i))
    (i : ι) :
    Multiset.card (Multiset.filter (· ∈ U i) (sumSubtype U m hn p : Multiset α)) = m i := by
  rw [filter_mem_sumSubtype h, Multiset.card_map]
  exact (p i).2

/-- Concatenation along a pairwise disjoint family is injective: each part of the tuple is
recovered by filtering on membership in the corresponding set. -/
theorem sumSubtype_injective (h : Pairwise (Function.onFun Disjoint U)) (hn : ∑ i, m i = n) :
    Function.Injective (sumSubtype U m hn) := by
  classical
  intro p q hpq
  funext i
  have hfilter := congrArg (fun w : Sym α n => Multiset.filter (· ∈ U i) (w : Multiset α)) hpq
  rw [filter_mem_sumSubtype h, filter_mem_sumSubtype h] at hfilter
  exact Sym.coe_injective (Multiset.map_injective Subtype.val_injective hfilter)

/-- A tuple supported in the union of a family, with exactly `m i` of its points
in `U i`, is a concatenation. -/
theorem exists_sumSubtype_eq [∀ i, DecidablePred (· ∈ U i)]
    (hn : ∑ i, m i = n) {w : Sym α n}
    (hw : ∀ a ∈ w, ∃ i, a ∈ U i)
    (hcard : ∀ i, Multiset.card (Multiset.filter (· ∈ U i) (w : Multiset α)) = m i) :
    ∃ p, sumSubtype U m hn p = w := by
  classical
  set A : ι → Multiset α := fun i => Multiset.filter (· ∈ U i) (w : Multiset α) with hA
  have hcardA : ∀ i, Multiset.card (A i) = m i := hcard
  have hsum : ∑ i, A i = (w : Multiset α) := by
    symm
    apply Multiset.eq_of_le_of_card_le
    · rw [Multiset.le_iff_count]
      intro a
      by_cases haw : a ∈ (w : Multiset α)
      · obtain ⟨i, hi⟩ := hw a (_root_.Sym.mem_coe.1 haw)
        rw [Multiset.count_sum']
        calc
          Multiset.count a (w : Multiset α) = Multiset.count a (A i) := by simp [hA, hi]
          _ ≤ ∑ j, Multiset.count a (A j) := by
            rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
            exact Nat.le_add_left _ _
      · simp [Multiset.count_eq_zero.2 haw]
    · simp only [Multiset.card_sum]
      rw [Finset.sum_congr rfl fun i _ => hcardA i, hn]
      exact Nat.le_of_eq w.2.symm
  have hrange : ∀ i, (⟨A i, hcardA i⟩ : Sym α (m i)) ∈
      Set.range (Sym.map (Subtype.val : U i → α)) := fun i =>
    (mem_range_map _).2 fun a ha =>
      ⟨⟨a, (Multiset.mem_filter.1 (_root_.Sym.mem_coe.1 ha)).2⟩, rfl⟩
  choose p hp using hrange
  refine ⟨p, Sym.coe_injective ?_⟩
  rw [coe_sumSubtype, ← hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa [Sym.coe_map] using congrArg (fun z : Sym α (m i) => (z : Multiset α)) (hp i)

/-- **Concatenation along a family, read on ordered tuples.** Along a bijection
`(Σ i, Fin (m i)) ≃ Fin n` the family of ordered tuples regroups into a single ordered `n`-tuple,
and concatenating the unordered tuples they present gives the unordered tuple it presents. -/
theorem sumSubtype_ofFn (hn : ∑ i, m i = n) (e : (Σ i, Fin (m i)) ≃ Fin n)
    (f : ∀ i, Fin (m i) → U i) :
    sumSubtype U m hn (fun i => ofFn (f i))
      = ofFn fun j : Fin n => ((f (e.symm j).1 (e.symm j).2 : α)) := by
  refine Sym.coe_injective ?_
  have hmap : ∀ i, ((ofFn (f i) : Sym (U i) (m i)) : Multiset (U i)).map Subtype.val
      = ∑ k : Fin (m i), ({(f i k : α)} : Multiset α) := fun i => by
    rw [coe_ofFn_eq_sum, ← Multiset.coe_mapAddMonoidHom (Subtype.val : U i → α), map_sum]
    simp
  rw [coe_sumSubtype, coe_ofFn_eq_sum, Finset.sum_congr rfl fun i _ => hmap i]
  calc ∑ i, ∑ k : Fin (m i), ({(f i k : α)} : Multiset α)
      = ∑ k : (Σ i, Fin (m i)), ({(f k.1 k.2 : α)} : Multiset α) := by
        rw [Finset.sum_sigma', Finset.univ_sigma_univ]
    _ = ∑ j : Fin n, ({(f (e.symm j).1 (e.symm j).2 : α)} : Multiset α) :=
        (Equiv.sum_comp e.symm _).symm

/-- The range of concatenation along a pairwise disjoint family: the unordered tuples supported in
the union of the family with exactly `m i` of their points in `U i`. -/
theorem mem_range_sumSubtype [∀ i, DecidablePred (· ∈ U i)]
    (h : Pairwise (Function.onFun Disjoint U)) (hn : ∑ i, m i = n) {w : Sym α n} :
    w ∈ Set.range (sumSubtype U m hn) ↔
      (∀ a ∈ w, ∃ i, a ∈ U i) ∧
        ∀ i, Multiset.card (Multiset.filter (· ∈ U i) (w : Multiset α)) = m i := by
  refine ⟨?_, fun hw => exists_sumSubtype_eq hn hw.1 hw.2⟩
  rintro ⟨p, rfl⟩
  exact ⟨fun a ha => exists_mem_of_mem_sumSubtype ha, card_filter_mem_sumSubtype h hn p⟩

end Sym

end TauCeti
