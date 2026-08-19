/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
involved: the composite is a carrier-independent prerequisite for the later family-by-family
construction.

Both steps of the recipe transport along an isomorphism, so the composite does too:
`TauCeti.FixedPointCandidate.congr` turns an isomorphism `ψ : G ≃* G'` intertwining `F` with an
endomorphism `F'` of `G'` into an isomorphism of the two candidates. The candidate therefore
depends only on the isomorphism class of the *pair* `(G, F)`, which is what lets a construction of
`(G, F)` be replaced by another realization of it without changing the group named. Comparison with
a group produced by an unrelated construction is instead
`TauCeti.DerivedCentralQuotient.mulEquivOfKerLeCenter`, which applies to the candidate verbatim
because `FixedPointCandidate` is a derived central quotient.

## Main definitions

* `TauCeti.FixedPointCandidate`: the derived central quotient of a fixed subgroup.
* `TauCeti.FixedPointCandidate.congr`: its transport along an isomorphism intertwining the two
  endomorphisms.
* `TauCeti.FixedPointCandidate.congrEnd`: the same, with the endomorphism carried along by
  conjugation rather than supplied.

## Main results

* `TauCeti.FixedPointCandidate.mulEquivId`: at the identity endomorphism the recipe returns the
  derived central quotient of the whole group.

## References

This is the composite prescribed by milestone L3 of `TauCetiRoadmap/CFSGStatement/README.md`, which
fixes `H_d = fixedSubgroup d.steinberg` and `d.Group = [H_d, H_d] / Z([H_d, H_d])`, with the centre
read as the centre of the derived subgroup rather than of `H_d`. The construction is standard; see
R. W. Carter, *Simple Groups of Lie Type*, and D. Gorenstein, R. Lyons and R. Solomon, *The
Classification of the Finite Simple Groups*.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- The candidate simple group attached to an endomorphism `F` of a group: the derived subgroup of
the fixed points of `F`, modulo the centre of that derived subgroup.

For the Steinberg endomorphisms constructed by the roadmap, this is the corresponding finite group
of Lie type outside the small parameters excluded by `LieTypeIndex.InStandardRange`; at those
parameters it can be trivial, nonsimple, a duplicate, or the separately indexed Tits group. None of
these properties is asserted here. -/
abbrev FixedPointCandidate (F : G →* G) : Type _ :=
  DerivedCentralQuotient ↥(fixedSubgroup F)

namespace FixedPointCandidate

variable {G' G'' : Type*} [Group G'] [Group G'']
variable {F : G →* G} {F' : G' →* G'} {F'' : G'' →* G''}

/-- The candidate simple group transported along an isomorphism intertwining the two
endomorphisms.

The isomorphism carries the fixed subgroup of the one onto the fixed subgroup of the other, and the
derived central quotient of isomorphic groups are isomorphic, so the candidate depends only on the
isomorphism class of the pair `(G, F)`. -/
def congr (ψ : G ≃* G') (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) :
    FixedPointCandidate F ≃* FixedPointCandidate F' :=
  DerivedCentralQuotient.congr (fixedSubgroupCongr ψ hψ)

@[simp]
theorem congr_mk (ψ : G ≃* G') (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G'))
    (x : ↥(commutator ↥(fixedSubgroup F))) :
    FixedPointCandidate.congr ψ hψ (x : FixedPointCandidate F) =
      (commutatorCongr (fixedSubgroupCongr ψ hψ) x : FixedPointCandidate F') := by
  simp only [FixedPointCandidate.congr, DerivedCentralQuotient.congr_mk]

@[simp]
theorem congr_refl (hψ : (MulEquiv.refl G : G →* G).comp F = F.comp (MulEquiv.refl G : G →* G)) :
    FixedPointCandidate.congr (MulEquiv.refl G) hψ = MulEquiv.refl (FixedPointCandidate F) := by
  rw [FixedPointCandidate.congr, fixedSubgroupCongr_refl, DerivedCentralQuotient.congr_refl]

theorem congr_trans (ψ : G ≃* G') (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G'))
    (χ : G' ≃* G'') (hχ : (χ : G' →* G'').comp F' = F''.comp (χ : G' →* G'')) :
    (FixedPointCandidate.congr ψ hψ).trans (FixedPointCandidate.congr χ hχ) =
      FixedPointCandidate.congr (ψ.trans χ) (MulEquiv.trans_comp_eq_comp_trans hψ hχ) := by
  rw [FixedPointCandidate.congr, FixedPointCandidate.congr, FixedPointCandidate.congr,
    DerivedCentralQuotient.congr_trans, fixedSubgroupCongr_trans]

theorem congr_symm (ψ : G ≃* G') (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) :
    (FixedPointCandidate.congr ψ hψ).symm =
      FixedPointCandidate.congr ψ.symm (MulEquiv.symm_comp_eq_comp_symm ψ hψ) := by
  rw [FixedPointCandidate.congr, FixedPointCandidate.congr, DerivedCentralQuotient.congr_symm,
    fixedSubgroupCongr_symm]

/-- The candidate simple group transported along an isomorphism of the ambient group, with the
endomorphism carried along by conjugation.

This is the form a consumer replacing one realization of a pinned group by another uses: only the
isomorphism of ambient groups has to be produced, and the Steinberg map on the other side is then
determined. -/
def congrEnd (ψ : G ≃* G') (F : G →* G) :
    FixedPointCandidate F ≃* FixedPointCandidate (MulEquiv.endCongr ψ F) :=
  FixedPointCandidate.congr ψ (MulEquiv.comp_eq_endCongr_comp ψ F)

/-- At the identity endomorphism the recipe returns the derived central quotient of the whole
group, since the identity fixes every point.

This is the degenerate end of the construction, and the reason the two steps are composed in the
stated order: no Steinberg endomorphism is involved, and what is left is exactly the
derived-subgroup-modulo-its-centre step. -/
def mulEquivId : FixedPointCandidate (MonoidHom.id G) ≃* DerivedCentralQuotient G :=
  DerivedCentralQuotient.congr
    ((MulEquiv.subgroupCongr (fixedSubgroup_eq_top_iff.mpr rfl)).trans Subgroup.topEquiv)

end FixedPointCandidate

end TauCeti
