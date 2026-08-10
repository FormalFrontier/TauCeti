/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.GroupTheory.DerivedCentralQuotient
public import TauCeti.GroupTheory.FixedSubgroup

/-!
# The candidate simple group attached to an endomorphism

For an endomorphism `F` of a group `G` this file composes the two constructions of
`TauCeti.GroupTheory.FixedSubgroup` and `TauCeti.GroupTheory.DerivedCentralQuotient` into

```text
FixedPointCandidate F = [H, H] / Z([H, H]),  where  H = fixedSubgroup F,
```

the group the classification's Lie-type lane attaches to a Steinberg endomorphism of a pinned
algebraic group. Nothing here asserts that the result is finite or simple, and no ambient group is
involved: the composite is carrier-independent, so it is available before any particular ambient
group has been constructed.

## Main definitions

* `TauCeti.FixedPointCandidate`: the derived central quotient of a fixed subgroup.
* `TauCeti.fixedPointCandidateCongr`: transport along an isomorphism intertwining two
  endomorphisms.

## Main results

* `TauCeti.fixedPointCandidateCongr`, together with its coherence laws
  `TauCeti.fixedPointCandidateCongr_refl`, `TauCeti.fixedPointCandidateCongr_symm` and
  `TauCeti.fixedPointCandidateCongr_trans`, says that the whole recipe depends on the endomorphism
  only up to intertwining isomorphism, hence not on the model of its input.
* `TauCeti.fixedPointCandidateMulEquivOfIsSimpleGroup`: the recipe returns fixed points that already
  form a nonabelian simple group unchanged.

## References

This is the composite prescribed by milestone L3 of `TauCetiRoadmap/CFSGStatement/README.md`, which
fixes `H_d = fixedSubgroup d.steinberg` and `d.Group = [H_d, H_d] / Z([H_d, H_d])`, with the centre
read as the centre of the derived subgroup rather than of `H_d`. The construction is standard; see
R. W. Carter, *Simple Groups of Lie Type*, and D. Gorenstein, R. Lyons and R. Solomon, *The
Classification of the Finite Simple Groups*.
-/

public section

namespace TauCeti

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

/-- The candidate simple group attached to an endomorphism `F` of a group: the derived subgroup of
the fixed points of `F`, modulo the centre of that derived subgroup.

For a Steinberg endomorphism of a pinned algebraic group over an algebraically closed field of
positive characteristic this is the corresponding finite group of Lie type; nothing of the sort is
asserted here. -/
abbrev FixedPointCandidate (F : G →* G) : Type _ :=
  DerivedCentralQuotient ↥(fixedSubgroup F)

/-- **The candidate attached to an endomorphism only depends on the endomorphism up to intertwining
isomorphism.** -/
def fixedPointCandidateCongr (e : G ≃* G') {F : G →* G} {F' : G' →* G'}
    (h : ∀ x, F' (e x) = e (F x)) : FixedPointCandidate F ≃* FixedPointCandidate F' :=
  DerivedCentralQuotient.congr (fixedSubgroupCongr e h)

@[simp]
theorem fixedPointCandidateCongr_mk (e : G ≃* G') {F : G →* G} {F' : G' →* G'}
    (h : ∀ x, F' (e x) = e (F x)) (x : ↥(commutator ↥(fixedSubgroup F))) :
    fixedPointCandidateCongr e h (x : FixedPointCandidate F) =
      (commutatorCongr (fixedSubgroupCongr e h) x : FixedPointCandidate F') := by
  simp only [fixedPointCandidateCongr, DerivedCentralQuotient.congr_mk]

@[simp]
theorem fixedPointCandidateCongr_refl {F : G →* G}
    (h : ∀ x, F (MulEquiv.refl G x) = MulEquiv.refl G (F x)) :
    fixedPointCandidateCongr (MulEquiv.refl G) h = MulEquiv.refl (FixedPointCandidate F) := by
  simp only [fixedPointCandidateCongr, fixedSubgroupCongr_refl,
    DerivedCentralQuotient.congr_refl]

@[simp]
theorem fixedPointCandidateCongr_symm (e : G ≃* G') {F : G →* G} {F' : G' →* G'}
    (h : ∀ x, F' (e x) = e (F x)) :
    (fixedPointCandidateCongr e h).symm =
      fixedPointCandidateCongr e.symm (symm_intertwines e h) := by
  simp only [fixedPointCandidateCongr, DerivedCentralQuotient.congr_symm,
    fixedSubgroupCongr_symm]

@[simp]
theorem fixedPointCandidateCongr_trans (e : G ≃* G') (e' : G' ≃* G'') {F : G →* G} {F' : G' →* G'}
    {F'' : G'' →* G''} (h : ∀ x, F' (e x) = e (F x)) (h' : ∀ y, F'' (e' y) = e' (F' y)) :
    (fixedPointCandidateCongr e h).trans (fixedPointCandidateCongr e' h') =
      fixedPointCandidateCongr (e.trans e') (trans_intertwines e e' h h') := by
  simp only [fixedPointCandidateCongr, DerivedCentralQuotient.congr_trans,
    fixedSubgroupCongr_trans]

/-- If the fixed points of `F` already form a nonabelian simple group, the recipe returns them. -/
def fixedPointCandidateMulEquivOfIsSimpleGroup (F : G →* G) [IsSimpleGroup ↥(fixedSubgroup F)]
    (h : ¬ IsMulCommutative ↥(fixedSubgroup F)) :
    FixedPointCandidate F ≃* ↥(fixedSubgroup F) :=
  DerivedCentralQuotient.mulEquivOfIsSimpleGroup h

end TauCeti
