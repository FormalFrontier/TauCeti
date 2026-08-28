/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.QuotientGroup.Defs

import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Tits systems

A **Tits system**, or **BN-pair**, in a group `G` consists of two subgroups `B` and `N` and a
set of lifts in `N` of the simple reflections of `W = N / (B ∩ N)`.  The subgroups generate
`G`, the intersection `B ∩ N` is normal in `N`, the simple lifts generate `N` modulo that
intersection and square into it, and the double cosets satisfy the Tits multiplication and
nondegeneracy axioms.

`TauCeti.TitsSystem` records the simple reflections by chosen lifts in `N`.  This avoids making
the structure depend on representatives chosen later, while `TauCeti.TitsSystem.WeylGroup` and
`TauCeti.TitsSystem.simple` recover the quotient and its representation-independent simple set.

## Main definitions

* `TauCeti.TitsSystem`: a Tits system with chosen lifts of its simple reflections.
* `TauCeti.TitsSystem.intersection`: the subgroup `B ∩ N`, regarded as a subgroup of `N`.
* `TauCeti.TitsSystem.WeylGroup`: the quotient `N / (B ∩ N)`.
* `TauCeti.TitsSystem.simple`: the simple reflections in the Weyl group.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 28.1.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Section 8.3.
-/

public section

open scoped Pointwise

namespace TauCeti

universe u

/-- A **Tits system** (or **BN-pair**) in `G`, with chosen lifts in `N` of its simple
reflections.

The field `mul_doubleCoset_subset` is the usual axiom
`B s B w B ⊆ B (s w) B ∪ B w B`.  Choosing lifts makes the generating and involution axioms
expressible before constructing the quotient `N / (B ∩ N)`; the resulting simple set in the
quotient is exposed by `TitsSystem.simple`. -/
@[ext]
structure TitsSystem (G : Type u) [Group G] where
  /-- The subgroup conventionally denoted `B`. -/
  subgroupB : Subgroup G
  /-- The subgroup conventionally denoted `N`. -/
  subgroupN : Subgroup G
  /-- Chosen lifts in `N` of the simple reflections. -/
  simpleReps : Set subgroupN
  /-- The subgroups `B` and `N` generate the ambient group. -/
  closure_subgroupB_union_subgroupN :
    Subgroup.closure ((subgroupB : Set G) ∪ subgroupN) = ⊤
  /-- The intersection `B ∩ N`, regarded inside `N`, is normal. -/
  intersection_normal : (subgroupB.comap subgroupN.subtype).Normal
  /-- The simple lifts together with `B ∩ N` generate `N`. -/
  closure_intersection_union_simpleReps :
    Subgroup.closure ((subgroupB.comap subgroupN.subtype : Set subgroupN) ∪ simpleReps) = ⊤
  /-- Every simple lift squares into `B ∩ N`. -/
  simpleRep_sq_mem (s : subgroupN) (hs : s ∈ simpleReps) :
    s * s ∈ subgroupB.comap subgroupN.subtype
  /-- Multiplying a Bruhat cell on the left by a simple cell produces at most the adjacent cell
  and the original cell. -/
  mul_doubleCoset_subset (s : subgroupN) (hs : s ∈ simpleReps) (w : subgroupN) :
    DoubleCoset.doubleCoset (s : G) subgroupB subgroupB *
        DoubleCoset.doubleCoset (w : G) subgroupB subgroupB ⊆
      DoubleCoset.doubleCoset ((s * w : subgroupN) : G) subgroupB subgroupB ∪
        DoubleCoset.doubleCoset (w : G) subgroupB subgroupB
  /-- No simple reflection conjugates `B` into `B`. -/
  exists_conj_not_mem (s : subgroupN) (hs : s ∈ simpleReps) :
    ∃ b : subgroupB, (s : G) * (b : G) * (s : G)⁻¹ ∉ subgroupB

namespace TitsSystem

variable {G : Type u} [Group G] (T : TitsSystem G)

/-- The intersection `B ∩ N`, regarded as a subgroup of `N`. -/
def intersection : Subgroup T.subgroupN :=
  T.subgroupB.comap T.subgroupN.subtype

/-- Membership in the intersection means membership in `B` after forgetting the `N` subtype. -/
@[simp]
theorem mem_intersection (n : T.subgroupN) : n ∈ T.intersection ↔ (n : G) ∈ T.subgroupB :=
  Iff.rfl

instance intersectionNormal : T.intersection.Normal :=
  T.intersection_normal

/-- The Weyl group `W = N / (B ∩ N)` of a Tits system. -/
abbrev WeylGroup :=
  T.subgroupN ⧸ T.intersection

/-- The simple reflections in the Weyl group, obtained from the chosen lifts. -/
def simple : Set T.WeylGroup :=
  QuotientGroup.mk' T.intersection '' T.simpleReps

/-- Membership in the simple set means being the image of a chosen simple representative. -/
@[simp]
theorem mem_simple (s : T.WeylGroup) :
    s ∈ T.simple ↔ ∃ r ∈ T.simpleReps, QuotientGroup.mk' T.intersection r = s :=
  Iff.rfl

/-- Every chosen simple representative maps to a simple reflection. -/
theorem mk_mem_simple (s : T.subgroupN) (hs : s ∈ T.simpleReps) :
    QuotientGroup.mk' T.intersection s ∈ T.simple :=
  (T.mem_simple _).2 ⟨s, hs, rfl⟩

/-- Every simple reflection has square one. -/
theorem simple_sq_eq_one {s : T.WeylGroup} (hs : s ∈ T.simple) : s * s = 1 := by
  obtain ⟨r, hr, rfl⟩ := (T.mem_simple _).1 hs
  rw [← map_mul]
  exact (QuotientGroup.eq_one_iff (N := T.intersection) (r * r)).mpr
    (T.simpleRep_sq_mem r hr)

/-- The simple reflections generate the Weyl group. -/
theorem closure_simple : Subgroup.closure T.simple = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective T.intersection w
  have hn : n ∈ Subgroup.closure
      ((T.subgroupB.comap T.subgroupN.subtype : Set T.subgroupN) ∪ T.simpleReps) := by
    rw [T.closure_intersection_union_simpleReps]
    exact Subgroup.mem_top n
  have hmap : QuotientGroup.mk' T.intersection n ∈
      (Subgroup.closure
        ((T.subgroupB.comap T.subgroupN.subtype : Set T.subgroupN) ∪ T.simpleReps)).map
          (QuotientGroup.mk' T.intersection) :=
    ⟨n, hn, rfl⟩
  rw [MonoidHom.map_closure] at hmap
  exact ((Subgroup.closure_le (Subgroup.closure T.simple)).mpr (fun x hx ↦ by
    obtain ⟨y, hy, rfl⟩ := hx
    rcases hy with hy | hy
    · have hy' : y ∈ T.intersection := (T.mem_intersection y).mpr hy
      have hqy : QuotientGroup.mk' T.intersection y = 1 :=
        (QuotientGroup.eq_one_iff y).mpr hy'
      rw [hqy]
      exact (Subgroup.closure T.simple).one_mem
    · exact Subgroup.subset_closure (T.mk_mem_simple y hy))) hmap

/-- A simple reflection is not the identity. -/
theorem simple_ne_one {s : T.WeylGroup} (hs : s ∈ T.simple) : s ≠ 1 := by
  obtain ⟨r, hr, rfl⟩ := (T.mem_simple _).1 hs
  intro heq
  have hsB : (r : G) ∈ T.subgroupB :=
    (T.mem_intersection r).mp ((QuotientGroup.eq_one_iff r).mp heq)
  obtain ⟨b, hb⟩ := T.exists_conj_not_mem r hr
  exact hb (T.subgroupB.mul_mem
    (T.subgroupB.mul_mem hsB b.property) (T.subgroupB.inv_mem hsB))

end TitsSystem

end TauCeti
