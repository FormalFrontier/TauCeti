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
set of simple reflections in `W = N / (B ∩ N)`.  The subgroups generate `G`, the intersection
`B ∩ N` is normal in `N`, the simple reflections generate `W` and are involutions, and the
double cosets satisfy the Tits multiplication and nondegeneracy axioms.

## Main definitions

* `TauCeti.TitsSystem`: a Tits system with its simple reflections in the Weyl quotient.
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

/-- A **Tits system** (or **BN-pair**) in `G`.

The field `mul_doubleCoset_subset` is the usual axiom
`B s B w B ⊆ B (s w) B ∪ B w B`.  Its representative is supplied existentially so the
structure records only the representation-independent simple set in `N / (B ∩ N)`. -/
@[ext]
structure TitsSystem (G : Type u) [Group G] where
  /-- The subgroup conventionally denoted `B`. -/
  subgroupB : Subgroup G
  /-- The subgroup conventionally denoted `N`. -/
  subgroupN : Subgroup G
  /-- The subgroups `B` and `N` generate the ambient group. -/
  closure_subgroupB_union_subgroupN :
    Subgroup.closure ((subgroupB : Set G) ∪ subgroupN) = ⊤
  /-- The intersection `B ∩ N`, regarded inside `N`, is normal. -/
  intersection_normal : (subgroupB.comap subgroupN.subtype).Normal
  /-- The simple reflections in the Weyl quotient `N / (B ∩ N)`. -/
  simple : Set (subgroupN ⧸ subgroupB.comap subgroupN.subtype)
  /-- The simple reflections generate the Weyl quotient. -/
  closure_simple :
    let _ := intersection_normal
    Subgroup.closure simple = ⊤
  /-- Every simple reflection has a representative whose square lies in `B ∩ N`. -/
  exists_simpleRep_sq_mem
      (s : subgroupN ⧸ subgroupB.comap subgroupN.subtype) (hs : s ∈ simple) :
    ∃ r : subgroupN,
      (QuotientGroup.mk r : subgroupN ⧸ subgroupB.comap subgroupN.subtype) = s ∧
        r * r ∈ subgroupB.comap subgroupN.subtype
  /-- Multiplying a Bruhat cell on the left by a simple cell produces at most the adjacent cell
  and the original cell. -/
  mul_doubleCoset_subset
      (s : subgroupN ⧸ subgroupB.comap subgroupN.subtype) (hs : s ∈ simple) :
    ∃ r : subgroupN,
      (QuotientGroup.mk r : subgroupN ⧸ subgroupB.comap subgroupN.subtype) = s ∧
        ∀ w : subgroupN,
          DoubleCoset.doubleCoset (r : G) subgroupB subgroupB *
              DoubleCoset.doubleCoset (w : G) subgroupB subgroupB ⊆
            DoubleCoset.doubleCoset ((r * w : subgroupN) : G) subgroupB subgroupB ∪
              DoubleCoset.doubleCoset (w : G) subgroupB subgroupB
  /-- No simple reflection conjugates `B` into `B`. -/
  exists_conj_not_mem
      (s : subgroupN ⧸ subgroupB.comap subgroupN.subtype) (hs : s ∈ simple) :
    ∃ r : subgroupN,
      (QuotientGroup.mk r : subgroupN ⧸ subgroupB.comap subgroupN.subtype) = s ∧
        ∃ b : subgroupB, (r : G) * (b : G) * (r : G)⁻¹ ∉ subgroupB

namespace TitsSystem

variable {G : Type u} [Group G] (T : TitsSystem G)

/-- The intersection `B ∩ N`, regarded as a subgroup of `N`. -/
abbrev intersection : Subgroup T.subgroupN :=
  T.subgroupB.comap T.subgroupN.subtype

/-- Membership in the intersection means membership in `B` after forgetting the `N` subtype. -/
theorem mem_intersection (n : T.subgroupN) : n ∈ T.intersection ↔ (n : G) ∈ T.subgroupB :=
  Iff.rfl

instance intersectionNormal : T.intersection.Normal :=
  T.intersection_normal

/-- The Weyl group `W = N / (B ∩ N)` of a Tits system. -/
abbrev WeylGroup :=
  T.subgroupN ⧸ T.intersection

/-- Every simple reflection has square one. -/
theorem simple_sq_eq_one {s : T.WeylGroup} (hs : s ∈ T.simple) : s * s = 1 := by
  obtain ⟨r, rfl, hr⟩ := T.exists_simpleRep_sq_mem s hs
  rw [← QuotientGroup.mk_mul]
  exact (QuotientGroup.eq_one_iff (N := T.intersection) (r * r)).mpr hr

/-- A simple reflection is not the identity. -/
theorem simple_ne_one {s : T.WeylGroup} (hs : s ∈ T.simple) : s ≠ 1 := by
  obtain ⟨r, hrs, b, hb⟩ := T.exists_conj_not_mem s hs
  intro heq
  have hr_one : QuotientGroup.mk' T.intersection r = 1 := hrs.trans heq
  have hsB : (r : G) ∈ T.subgroupB :=
    (T.mem_intersection r).mp ((QuotientGroup.eq_one_iff r).mp hr_one)
  exact hb (T.subgroupB.mul_mem
    (T.subgroupB.mul_mem hsB b.property) (T.subgroupB.inv_mem hsB))

end TitsSystem

end TauCeti
