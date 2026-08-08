/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Algebra.Group.NormalizerQuotient.Conjugation

/-!
# Basepoint change for fundamental-group subgroups

The pointed classification of connected covers records a subgroup of the fundamental group at
a chosen basepoint. Changing the basepoint along a path transports that subgroup by the
standard path-conjugation isomorphism of fundamental groups. This file packages that transport
and the induced transport of the normalizer quotient `N(H) / H` used for deck groups of covers
attached to subgroups.

Mathlib already supplies the fundamental-group isomorphism
`FundamentalGroup.fundamentalGroupMulEquivOfPath`; the declarations here are only the
subgroup and normalizer-quotient bookkeeping needed by the universal-covers roadmap.

## Main declarations

* `TauCeti.FundamentalGroup.basepointChangeSubgroup`: transport a subgroup of `π₁(X, x₀)`
  along a path `γ : Path x₀ x₁`.
* Domain-specific membership, inclusion, monotonicity, and normality lemmas for
  `basepointChangeSubgroup`.
* `TauCeti.FundamentalGroup.basepointChangeNormalizerQuotientEquiv`: the corresponding
  isomorphism `N(H) / H ≃* N(γ₊H) / γ₊H`.
* `TauCeti.FundamentalGroup.mem_basepointChangeSubgroup` and the representative `[simp]`
  lemmas for membership and quotient calculations under these domain-specific names.

## References

This supplies a small prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
items 7 and 8: the pointed cover attached to `H ≤ π₁(X, x₀)`, conjugacy under basepoint
change, and the normalizer quotient `N(H) / H` appearing as the deck group of that cover.
-/

public section

namespace TauCeti

namespace FundamentalGroup

variable {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}

/-- The subgroup of `π₁(X, x₁)` obtained from `H ≤ π₁(X, x₀)` by changing basepoint along a
path `γ : Path x₀ x₁`. This is the subgroup-level form of conjugating loops by `γ`. -/
noncomputable def basepointChangeSubgroup (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup (_root_.FundamentalGroup X x₁) :=
  H.map (((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) :
    _root_.FundamentalGroup X x₀ →* _root_.FundamentalGroup X x₁))

/-- Membership in the subgroup transported along a basepoint-change path. -/
lemma mem_basepointChangeSubgroup (γ : Path x₀ x₁) (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.FundamentalGroup X x₁) :
    g ∈ basepointChangeSubgroup γ H ↔
      ∃ h ∈ H, _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ h = g :=
  Iff.rfl

/-- Membership in a transported subgroup, expressed by applying the inverse basepoint-change
isomorphism. -/
@[simp]
lemma mem_basepointChangeSubgroup_iff (γ : Path x₀ x₁) (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.FundamentalGroup X x₁) :
    g ∈ basepointChangeSubgroup γ H ↔
      (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm g ∈ H := by
  simpa [basepointChangeSubgroup] using
    (Subgroup.mem_map_equiv
      (f := _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) (K := H) (x := g))

/-- A subgroup of the target fundamental group is contained in the transported subgroup iff
its inverse basepoint-change image is contained in the original subgroup. -/
lemma le_basepointChangeSubgroup_iff (γ : Path x₀ x₁) (K : Subgroup (_root_.FundamentalGroup X x₁))
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    K ≤ basepointChangeSubgroup γ H ↔
      K.map (((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ).symm) :
        _root_.FundamentalGroup X x₁ →* _root_.FundamentalGroup X x₀) ≤ H := by
  rw [basepointChangeSubgroup]
  constructor
  · intro h x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyK, rfl⟩
    exact (Subgroup.mem_map_equiv
      (f := _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) (K := H)
        (x := y)).mp (h hyK)
  · intro h y hy
    exact (Subgroup.mem_map_equiv
      (f := _root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) (K := H)
        (x := y)).mpr (h (Subgroup.mem_map_of_mem _ hy))

/-- The transported subgroup is contained in a target subgroup iff the original subgroup is
contained in the target subgroup's inverse image under basepoint change. -/
lemma basepointChangeSubgroup_le_iff (γ : Path x₀ x₁) (H : Subgroup (_root_.FundamentalGroup X x₀))
    (K : Subgroup (_root_.FundamentalGroup X x₁)) :
    basepointChangeSubgroup γ H ≤ K ↔
      H ≤ K.comap (((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) :
        _root_.FundamentalGroup X x₀ →* _root_.FundamentalGroup X x₁)) := by
  rw [basepointChangeSubgroup, Subgroup.map_le_iff_le_comap]

/-- Basepoint-change transport is monotone on subgroups. -/
lemma basepointChangeSubgroup_mono (γ : Path x₀ x₁)
    {H K : Subgroup (_root_.FundamentalGroup X x₀)} (h : H ≤ K) :
    basepointChangeSubgroup γ H ≤ basepointChangeSubgroup γ K := by
  rw [basepointChangeSubgroup, basepointChangeSubgroup]
  exact Subgroup.map_mono h

/-- Normality is invariant under basepoint-change transport. -/
lemma basepointChangeSubgroup_normal_iff (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    (basepointChangeSubgroup γ H).Normal ↔ H.Normal := by
  rw [basepointChangeSubgroup]
  exact MulEquiv.normal_map_iff

/-- A normal subgroup remains normal after basepoint-change transport. -/
lemma basepointChangeSubgroup.normal (γ : Path x₀ x₁)
    {H : Subgroup (_root_.FundamentalGroup X x₀)} (hH : H.Normal) :
    (basepointChangeSubgroup γ H).Normal :=
  (basepointChangeSubgroup_normal_iff γ H).2 hH

/-- The normalizer quotient `N(H) / H` transported along a basepoint-change path. -/
noncomputable def basepointChangeNormalizerQuotientEquiv (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) :
    Subgroup.normalizerQuotient H ≃*
      Subgroup.normalizerQuotient (basepointChangeSubgroup γ H) :=
  (Subgroup.normalizerQuotientEquivMap H
    (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ)).trans
    (Subgroup.normalizerQuotientCongr (by rw [basepointChangeSubgroup]))

/-- On normalizer representatives, basepoint-change transport is induced by the
path-conjugation isomorphism of fundamental groups. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_mk (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.Subgroup.normalizer (H : Set (_root_.FundamentalGroup X x₀))) :
    basepointChangeNormalizerQuotientEquiv γ H (g : Subgroup.normalizerQuotient H) =
      ((MulEquiv.subgroupCongr (by rw [basepointChangeSubgroup])
          (Subgroup.normalizerEquivMap H
            (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g) :
          _root_.Subgroup.normalizer
            ((basepointChangeSubgroup γ H) : Set (_root_.FundamentalGroup X x₁))) :
        Subgroup.normalizerQuotient (basepointChangeSubgroup γ H)) := by
  rw [← Subgroup.normalizerQuotientMk_apply, ← Subgroup.normalizerQuotientMk_apply,
    basepointChangeNormalizerQuotientEquiv, MulEquiv.trans_apply,
    Subgroup.normalizerQuotientEquivMap_mk,
    Subgroup.normalizerQuotientCongr_mk]

/-- The inverse basepoint-change transport sends a target representative to the inverse
path-conjugation representative. -/
@[simp]
lemma basepointChangeNormalizerQuotientEquiv_symm_mk (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀)) (g : _root_.Subgroup.normalizer
      ((basepointChangeSubgroup γ H) : Set (_root_.FundamentalGroup X x₁))) :
    (basepointChangeNormalizerQuotientEquiv γ H).symm
        (g : Subgroup.normalizerQuotient (basepointChangeSubgroup γ H)) =
      (((Subgroup.normalizerEquivMap H
          (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ)).symm
          ((MulEquiv.subgroupCongr (by rw [basepointChangeSubgroup])).symm g)) :
        Subgroup.normalizerQuotient H) := by
  rw [← Subgroup.normalizerQuotientMk_apply, ← Subgroup.normalizerQuotientMk_apply,
    basepointChangeNormalizerQuotientEquiv, MulEquiv.symm_trans_apply,
    Subgroup.normalizerQuotientCongr_symm_mk, Subgroup.normalizerQuotientEquivMap_symm_mk]
  -- The forward and inverse `subgroupCongr` agree on representatives (both are the identity on
  -- underlying elements), so the two transported representatives coincide.
  rfl

/-- On representatives, basepoint-change transport applies the path-conjugation isomorphism
of fundamental groups. -/
lemma basepointChangeNormalizerQuotientEquiv_mk_coe (γ : Path x₀ x₁)
    (H : Subgroup (_root_.FundamentalGroup X x₀))
    (g : _root_.Subgroup.normalizer (H : Set (_root_.FundamentalGroup X x₀))) :
    basepointChangeNormalizerQuotientEquiv γ H (Subgroup.normalizerQuotientMk H g) =
      Subgroup.normalizerQuotientMk (basepointChangeSubgroup γ H)
        (MulEquiv.subgroupCongr (by rw [basepointChangeSubgroup])
          (⟨_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ
              (g : _root_.FundamentalGroup X x₀),
            by
              rw [← Subgroup.normalizerEquivMap_apply_coe H
                (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g]
              exact (Subgroup.normalizerEquivMap H
                (_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) g).2⟩ :
            _root_.Subgroup.normalizer
              ((H.map ((_root_.FundamentalGroup.fundamentalGroupMulEquivOfPath γ) :
                _root_.FundamentalGroup X x₀ →* _root_.FundamentalGroup X x₁)) :
                  Set (_root_.FundamentalGroup X x₁)))) := by
  rw [basepointChangeNormalizerQuotientEquiv, MulEquiv.trans_apply,
    Subgroup.normalizerQuotientEquivMap_mk_coe,
    Subgroup.normalizerQuotientCongr_mk]

end FundamentalGroup

end TauCeti
