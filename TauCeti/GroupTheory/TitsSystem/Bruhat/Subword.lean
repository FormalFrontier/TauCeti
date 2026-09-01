/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Bruhat.Basic

/-!
# Subword expansion of products of Bruhat cells

For a Tits system, inversion carries the Bruhat cell indexed by `w` to the cell indexed by
`w⁻¹`. Consequently the left-handed rank-one multiplication law also holds on the right: if `s`
is simple, then `(B w B)(B s B)` is either `B (w s) B` or its union with `B w B`.

Iterating the rank-one law gives the subword expansion needed for the uniqueness part of Bruhat
decomposition. If `s₁, …, sₙ` are simple, every element of

```text
(B s₁ B) ⋯ (B sₙ B)
```

lies in the cell indexed by the product of some subword of `s₁, …, sₙ`. No reducedness
hypothesis is needed for this upper bound.

## Main results

* `TauCeti.TitsSystem.inv_bruhatCell`: inversion of a Weyl-indexed cell.
* `TauCeti.TitsSystem.bruhatCell_mul_eq_or_eq_union_of_mem_simple_right`: right multiplication
  by a simple cell.
* `TauCeti.TitsSystem.exists_sublist_of_mem_prod_bruhatCell`: the subword expansion for a product
  of simple cells.

## Roadmap

This is the next combinatorial input toward injectivity of the Weyl-to-double-coset map and the
Coxeter-system consequences of a Tits system in Layer 7, "Bruhat decomposition and BN-pairs /
Tits systems", of `TauCetiRoadmap/ReductiveGroups/README.md`.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Sections 29.1--29.2.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Section 8.3.
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

/-- Inversion carries the Bruhat cell indexed by `w` to the cell indexed by `w⁻¹`. -/
@[simp]
theorem inv_bruhatCell (w : T.WeylGroup) : (T.bruhatCell w)⁻¹ = T.bruhatCell w⁻¹ := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective T.intersection w
  simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, T.bruhatCell_mk]
  simp only [DoubleCoset.doubleCoset, mul_inv_rev, Set.inv_singleton, inv_coe_set,
    Subgroup.coe_inv, mul_assoc]

/-- **Right multiplication by a simple Bruhat cell.** For a Weyl-group element `w` and a simple
reflection `s`, the product of their cells is either the cell at `w * s` or its union with the
cell at `w`. -/
theorem bruhatCell_mul_eq_or_eq_union_of_mem_simple_right (w : T.WeylGroup)
    {s : T.WeylGroup} (hs : s ∈ T.simple) :
    T.bruhatCell w * T.bruhatCell s = T.bruhatCell (w * s) ∨
      T.bruhatCell w * T.bruhatCell s = T.bruhatCell (w * s) ∪ T.bruhatCell w := by
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (T.simple_sq_eq_one hs)
  rcases T.bruhatCell_mul_eq_or_eq_union_of_mem_simple hs w⁻¹ with h | h
  · left
    have h' := congrArg Inv.inv h
    simpa only [mul_inv_rev, inv_bruhatCell, inv_inv, hs_inv] using h'
  · right
    have h' := congrArg Inv.inv h
    simpa only [mul_inv_rev, inv_bruhatCell, inv_inv, hs_inv, Set.union_inv] using h'

/-- The product of simple Bruhat cells is contained in the union of the cells indexed by
subwords. Explicitly, every element of that product lies in the cell indexed by the product of
some sublist of the original word. -/
theorem exists_sublist_of_mem_prod_bruhatCell {l : List T.WeylGroup}
    (hs : ∀ s ∈ l, s ∈ T.simple) {g : G}
    (hg : g ∈ (l.map T.bruhatCell).prod) :
    ∃ q : List T.WeylGroup, List.Sublist q l ∧ g ∈ T.bruhatCell q.prod := by
  induction l generalizing g with
  | nil =>
      simp only [List.map_nil, List.prod_nil, Set.mem_one] at hg
      subst g
      refine ⟨[], List.Sublist.refl [], ?_⟩
      simp only [List.prod_nil, bruhatCell_one]
      exact T.subgroupB.one_mem
  | cons s l ih =>
      have hsimple : s ∈ T.simple := hs s (List.mem_cons_self)
      have htail : ∀ t ∈ l, t ∈ T.simple := fun t ht => hs t (List.mem_cons_of_mem s ht)
      rw [List.map_cons, List.prod_cons] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      obtain ⟨q, hql, hbq⟩ := ih htail hb
      have hab : a * b ∈ T.bruhatCell s * T.bruhatCell q.prod := ⟨a, ha, b, hbq, rfl⟩
      rcases T.bruhatCell_mul_eq_or_eq_union_of_mem_simple hsimple q.prod with h | h
      · refine ⟨s :: q, hql.cons_cons s, ?_⟩
        rw [List.prod_cons, ← h]
        exact hab
      · rw [h] at hab
        rcases hab with hab | hab
        · exact ⟨s :: q, hql.cons_cons s, by simpa only [List.prod_cons] using hab⟩
        · exact ⟨q, hql.cons s, hab⟩

end TauCeti.TitsSystem
