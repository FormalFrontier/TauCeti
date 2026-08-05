/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The normalizer quotient of a subgroup

This file packages the algebraic quotient `N(H) / H`, where `N(H)` is the normalizer of a
subgroup `H ≤ G`. This is the group that occurs in the universal-covers roadmap when the
deck group of the connected cover associated to `H ≤ π₁(X, x₀)` is identified with
`N(H) / H`.

The construction is deliberately only a thin local API around Mathlib's `Subgroup.normalizer`,
`Subgroup.subgroupOf`, and quotient groups. Mathlib already proves that `H` is normal in its
normalizer; this file gives the quotient a stable name and records its canonical quotient map,
an equality criterion by multiplication by an element of `H`, and the comparison with `G / H`
in the normal case.

## Main declarations

* `TauCeti.Subgroup.normalizerQuotient`: the quotient `N(H) / H`.
* `TauCeti.Subgroup.normalizerQuotientMk`: the canonical map `N(H) →* N(H) / H`.
* `TauCeti.Subgroup.normalizerQuotientLift`: the universal property for maps out of
  `N(H) / H`.
* `TauCeti.Subgroup.normalizerQuotientToQuotientOfNormal`: when `H` is normal in `G`,
  the natural map `N(H) / H →* G / H`.
* `TauCeti.Subgroup.normalizerQuotientEquivQuotientOfNormal`: when `H` is normal in `G`,
  the normalizer quotient is canonically isomorphic to `G / H`.

## References

This supplies the algebraic normalizer-quotient prerequisite named in
`TauCetiRoadmap/UniversalCovers/README.md`, Stage 2: for the cover associated to
`H ≤ π₁(X, x₀)`, the deck group is `N(H) / H`, and in the regular case `H ◁ π₁(X, x₀)`
this becomes `π₁(X, x₀) / H`.
-/

public section

namespace TauCeti

namespace Subgroup

variable {G : Type*} [Group G]

/-- The normalizer quotient `N(H) / H` of a subgroup `H ≤ G`. Here `H` is viewed as a normal
subgroup of its normalizer, using Mathlib's `Subgroup.normal_in_normalizer` instance. -/
abbrev normalizerQuotient (H : Subgroup G) : Type _ :=
  _root_.Subgroup.normalizer (H : Set G) ⧸
    H.subgroupOf (_root_.Subgroup.normalizer (H : Set G))

/-- The canonical quotient map from the normalizer of `H` to `N(H) / H`. -/
abbrev normalizerQuotientMk (H : Subgroup G) :
    _root_.Subgroup.normalizer (H : Set G) →* normalizerQuotient H :=
  QuotientGroup.mk' (H.subgroupOf (_root_.Subgroup.normalizer (H : Set G)))

/-- The canonical quotient map evaluates as the quotient-group constructor. -/
@[simp]
lemma normalizerQuotientMk_apply (H : Subgroup G) (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientMk H g = (g : normalizerQuotient H) :=
  rfl

/-- A normalizer element maps to the identity in `N(H) / H` exactly when its underlying
element of `G` lies in `H`. -/
lemma normalizerQuotientMk_eq_one_iff (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientMk H g = 1 ↔ (g : G) ∈ H := by
  simp [normalizerQuotientMk, normalizerQuotient, _root_.Subgroup.mem_subgroupOf,
    QuotientGroup.eq_one_iff]

/-- The kernel of the quotient map `N(H) →* N(H) / H` is the copy of `H` inside its
normalizer. -/
lemma normalizerQuotientMk_ker (H : Subgroup G) : (normalizerQuotientMk H).ker =
      H.subgroupOf (_root_.Subgroup.normalizer (H : Set G)) := by
  exact QuotientGroup.ker_mk'
    (N := H.subgroupOf (_root_.Subgroup.normalizer (H : Set G)))

/-- Every element of `N(H) / H` is represented by an element of the normalizer. -/
lemma normalizerQuotientMk_surjective (H : Subgroup G) :
    Function.Surjective (normalizerQuotientMk H) :=
  QuotientGroup.mk'_surjective
    (H.subgroupOf (_root_.Subgroup.normalizer (H : Set G)))

/-- The canonical map `N(H) →* N(H) / H` has full range. -/
lemma normalizerQuotientMk_range (H : Subgroup G) : (normalizerQuotientMk H).range = ⊤ :=
  QuotientGroup.range_mk'
    (N := H.subgroupOf (_root_.Subgroup.normalizer (H : Set G)))

variable {M : Type*} [Group M]

/-- The universal property of `N(H) / H`: a homomorphism from the normalizer that sends every
ambient element of `H` to `1` descends to a homomorphism from the normalizer quotient. -/
abbrev normalizerQuotientLift (H : Subgroup G) (φ : _root_.Subgroup.normalizer (H : Set G) →* M)
    (hφ : ∀ g : _root_.Subgroup.normalizer (H : Set G), (g : G) ∈ H → φ g = 1) :
    normalizerQuotient H →* M :=
  QuotientGroup.lift (H.subgroupOf (_root_.Subgroup.normalizer (H : Set G))) φ (by
    intro g hg
    exact hφ g hg)

/-- The lift from `N(H) / H` evaluates on representatives as the original homomorphism. -/
@[simp]
lemma normalizerQuotientLift_mk (H : Subgroup G) (φ : _root_.Subgroup.normalizer (H : Set G) →* M)
    (hφ : ∀ g : _root_.Subgroup.normalizer (H : Set G), (g : G) ∈ H → φ g = 1)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientLift H φ hφ (normalizerQuotientMk H g) = φ g :=
  rfl

/-- The lift from `N(H) / H`, composed with the quotient map, is the original homomorphism
from the normalizer. -/
@[simp]
lemma normalizerQuotientLift_comp_mk (H : Subgroup G)
    (φ : _root_.Subgroup.normalizer (H : Set G) →* M)
    (hφ : ∀ g : _root_.Subgroup.normalizer (H : Set G), (g : G) ∈ H → φ g = 1) :
    (normalizerQuotientLift H φ hφ).comp (normalizerQuotientMk H) = φ :=
  rfl

/-- A lift from `N(H) / H` is surjective when the original homomorphism from the normalizer is
surjective. -/
lemma normalizerQuotientLift_surjective_of_surjective (H : Subgroup G)
    (φ : _root_.Subgroup.normalizer (H : Set G) →* M)
    (hφ : ∀ g : _root_.Subgroup.normalizer (H : Set G), (g : G) ∈ H → φ g = 1)
    (hφsurj : Function.Surjective φ) :
    Function.Surjective (normalizerQuotientLift H φ hφ) :=
  QuotientGroup.lift_surjective_of_surjective
    (H.subgroupOf (_root_.Subgroup.normalizer (H : Set G))) φ hφsurj (by
      intro g hg
      exact hφ g hg)

/-- A lift from `N(H) / H` is injective exactly when the only normalizer elements killed by
the original homomorphism are the elements of `H`. -/
lemma normalizerQuotientLift_injective_iff (H : Subgroup G)
    (φ : _root_.Subgroup.normalizer (H : Set G) →* M)
    (hφ : ∀ g : _root_.Subgroup.normalizer (H : Set G), (g : G) ∈ H → φ g = 1) :
    Function.Injective (normalizerQuotientLift H φ hφ) ↔
      ∀ g : _root_.Subgroup.normalizer (H : Set G), φ g = 1 ↔ (g : G) ∈ H := by
  rw [QuotientGroup.injective_lift_iff]
  · constructor
    · intro hker g
      constructor
      · intro hg
        have : g ∈ H.subgroupOf (_root_.Subgroup.normalizer (H : Set G)) := by
          rw [hker]
          exact hg
        exact this
      · exact hφ g
    · intro hker
      ext g
      exact (hker g).symm

/-- The quotient equality criterion for representatives in the normalizer, stated in the
ambient group `G`. -/
lemma normalizerQuotientMk_eq_iff_div_mem (H : Subgroup G)
    (g k : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientMk H g = normalizerQuotientMk H k ↔ (g : G) / (k : G) ∈ H := by
  simpa [normalizerQuotientMk, normalizerQuotient, _root_.Subgroup.mem_subgroupOf]
    using QuotientGroup.eq_iff_div_mem
      (N := H.subgroupOf (_root_.Subgroup.normalizer (H : Set G))) (x := g) (y := k)

/-- A version of the equality criterion using multiplication by an element of `H`. -/
lemma normalizerQuotientMk_eq_iff_exists_mul (H : Subgroup G)
    (g k : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientMk H g = normalizerQuotientMk H k ↔
      ∃ h ∈ H, h * (k : G) = g := by
  rw [normalizerQuotientMk_eq_iff_div_mem]
  constructor
  · intro hgk
    exact ⟨(g : G) / k, hgk, by simp [div_eq_mul_inv, mul_assoc]⟩
  · rintro ⟨h, hh, hg⟩
    rw [← hg]
    simpa [div_eq_mul_inv, mul_assoc] using hh

/-- Equal subgroups have canonically equivalent normalizer quotients, by transporting both the
normalizer and the distinguished subgroup inside it across the equality. -/
noncomputable abbrev normalizerQuotientCongr {H K : Subgroup G} (h : H = K) :
    normalizerQuotient H ≃* normalizerQuotient K :=
  QuotientGroup.congr
    (H.subgroupOf (_root_.Subgroup.normalizer (H : Set G)))
    (K.subgroupOf (_root_.Subgroup.normalizer (K : Set G)))
    (MulEquiv.subgroupCongr (by rw [h]))
    (by
      subst h
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩)

/-- The equal-subgroup congruence on normalizer quotients sends representatives to the
corresponding representatives under the normalizer congruence. -/
@[simp]
lemma normalizerQuotientCongr_mk {H K : Subgroup G} (h : H = K)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientCongr h (normalizerQuotientMk H g) =
      normalizerQuotientMk K (MulEquiv.subgroupCongr (by rw [h]) g) :=
  rfl

/-- The inverse equal-subgroup congruence on normalizer quotients sends representatives to the
corresponding representatives under the inverse normalizer congruence. -/
lemma normalizerQuotientCongr_symm_mk {H K : Subgroup G} (h : H = K)
    (g : _root_.Subgroup.normalizer (K : Set G)) :
    (normalizerQuotientCongr h).symm (normalizerQuotientMk K g) =
      normalizerQuotientMk H (MulEquiv.subgroupCongr (by rw [h]) g) :=
  rfl

section Normal

variable (H : Subgroup G) [H.Normal]

/-- When `H` is normal in `G`, the normalizer quotient maps naturally to the ordinary quotient
`G / H` by forgetting that representatives lie in the normalizer. -/
abbrev normalizerQuotientToQuotientOfNormal :
    normalizerQuotient H →* G ⧸ H :=
  QuotientGroup.map (H.subgroupOf (_root_.Subgroup.normalizer (H : Set G))) H
    (_root_.Subgroup.normalizer (H : Set G)).subtype
    (by
      intro g hg
      exact hg)

/-- The comparison map from `N(H) / H` to `G / H` sends a normalizer representative to its
ordinary quotient class. -/
@[simp]
lemma normalizerQuotientToQuotientOfNormal_mk (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientToQuotientOfNormal H (normalizerQuotientMk H g) =
      QuotientGroup.mk' H (g : G) :=
  rfl

/-- The ordinary quotient map `G →* G / H`, factored through the normalizer under normality,
agrees with the comparison map from `N(H) / H`. -/
@[simp]
lemma normalizerQuotientToQuotientOfNormal_comp_mk :
    (normalizerQuotientToQuotientOfNormal H).comp (normalizerQuotientMk H) =
      (QuotientGroup.mk' H).comp (_root_.Subgroup.normalizer (H : Set G)).subtype :=
  rfl

/-- If `H` is normal in `G`, then `N(H) / H` is canonically isomorphic to `G / H`. This is
the algebraic form of the regular-cover specialization from `N(H) / H` to `π₁(X, x₀) / H`. -/
noncomputable abbrev normalizerQuotientEquivQuotientOfNormal :
    normalizerQuotient H ≃* G ⧸ H :=
  QuotientGroup.congr
    (H.subgroupOf (_root_.Subgroup.normalizer (H : Set G))) H
    ((MulEquiv.subgroupCongr (_root_.Subgroup.normalizer_eq_top (H := H))).trans
      Subgroup.topEquiv)
    (by
      ext g
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact hk
      · intro hg
        exact ⟨⟨g, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩, hg, rfl⟩)

/-- The normal-case equivalence sends a normalizer representative to its ordinary quotient
class in `G / H`. -/
lemma normalizerQuotientEquivQuotientOfNormal_mk (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientEquivQuotientOfNormal H (normalizerQuotientMk H g) =
      QuotientGroup.mk' H (g : G) :=
  rfl

/-- The inverse normal-case equivalence sends an ordinary quotient representative to the
corresponding representative in the normalizer quotient. -/
lemma normalizerQuotientEquivQuotientOfNormal_symm_mk (g : G) :
    (normalizerQuotientEquivQuotientOfNormal H).symm (QuotientGroup.mk' H g) =
      normalizerQuotientMk H ⟨g, by simp [_root_.Subgroup.normalizer_eq_top (H := H)]⟩ :=
  rfl

end Normal

end Subgroup

end TauCeti
