/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Group.NormalizerQuotient.Basic

/-!
# Transporting normalizer quotients along group isomorphisms

The universal-covers roadmap uses the algebraic quotient `N(H) / H` as the deck group of the
cover attached to a subgroup `H`. When subgroups are transported by a basepoint change or by
an isomorphism of covers, the corresponding normalizer quotients have to be identified.

This file records the generic group-theoretic transport: a multiplicative equivalence
`e : G ≃* K` carries `N(H)` to `N(e(H))`, and therefore induces a multiplicative equivalence
`N(H) / H ≃* N(e(H)) / e(H)`.

## Main declarations

* `TauCeti.Subgroup.normalizerEquivMap`: the normalizer of `H` is identified with the
  normalizer of `H.map e`.
* `TauCeti.Subgroup.normalizerQuotientEquivMap`: the induced equivalence of normalizer
  quotients.
* Representative formulas, including compatibility with composition, inverse, and identity
  equivalences on representatives.

## References

This is the algebraic conjugacy bookkeeping needed by
`TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8: the unpointed cover
correspondence identifies subgroups only up to conjugacy, and the deck group of the cover
attached to `H` is `N(H) / H`.
-/

public section

namespace TauCeti

namespace Subgroup

variable {G K L : Type*} [Group G] [Group K] [Group L]

/-- A group isomorphism identifies the normalizer of a subgroup with the normalizer of its
image. -/
noncomputable abbrev normalizerEquivMap (H : Subgroup G) (e : G ≃* K) :
    _root_.Subgroup.normalizer (H : Set G) ≃*
      _root_.Subgroup.normalizer ((H.map (e : G →* K)) : Set K) :=
  (e.subgroupMap (_root_.Subgroup.normalizer (H : Set G))).trans
    (MulEquiv.subgroupCongr (_root_.Subgroup.map_equiv_normalizer_eq H e))

/-- On underlying group elements, `normalizerEquivMap` is the given group isomorphism. -/
@[simp]
lemma normalizerEquivMap_apply_coe (H : Subgroup G) (e : G ≃* K)
    (g : _root_.Subgroup.normalizer (H : Set G)) : (normalizerEquivMap H e g : K) = e (g : G) :=
  rfl

/-- On underlying group elements, the inverse of `normalizerEquivMap` is the inverse group
isomorphism. -/
@[simp]
lemma normalizerEquivMap_symm_apply_coe (H : Subgroup G) (e : G ≃* K)
    (k : _root_.Subgroup.normalizer ((H.map (e : G →* K)) : Set K)) :
    ((normalizerEquivMap H e).symm k : G) = e.symm (k : K) :=
  rfl

/-- Transporting normalizer representatives along the identity group isomorphism is the identity
on underlying representatives. -/
@[simp]
lemma normalizerEquivMap_refl (H : Subgroup G) (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerEquivMap H (MulEquiv.refl G) g =
      ⟨(g : G), by simp [g.2]⟩ := by
  ext
  rfl

/-- Transporting a normalizer representative through two group isomorphisms has underlying value
`f (e g)`. -/
@[simp]
lemma normalizerEquivMap_trans_apply_coe (H : Subgroup G) (e : G ≃* K) (f : K ≃* L)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    (normalizerEquivMap (H.map (e : G →* K)) f (normalizerEquivMap H e g) : L) =
      f (e (g : G)) :=
  rfl

/-- Rephrasing the inverse of `normalizerEquivMap` as transport along the inverse group
isomorphism sends a representative to its inverse image. -/
@[simp]
lemma normalizerEquivMap_symm_apply_coe' (H : Subgroup G) (e : G ≃* K)
    (k : _root_.Subgroup.normalizer ((H.map (e : G →* K)) : Set K)) :
    (normalizerEquivMap (H.map (e : G →* K)) e.symm k : G) = e.symm (k : K) :=
  rfl

/-- The copy of `H` inside its normalizer maps to the copy of `e(H)` inside the target
normalizer. -/
lemma subgroupOf_map_normalizerEquivMap (H : Subgroup G) (e : G ≃* K) :
    (H.subgroupOf (_root_.Subgroup.normalizer (H : Set G))).map ((normalizerEquivMap H e :
          _root_.Subgroup.normalizer (H : Set G) ≃*
            _root_.Subgroup.normalizer ((H.map (e : G →* K)) : Set K)) :
          _root_.Subgroup.normalizer (H : Set G) →*
            _root_.Subgroup.normalizer ((H.map (e : G →* K)) : Set K)) =
      (H.map (e : G →* K)).subgroupOf
        (_root_.Subgroup.normalizer ((H.map (e : G →* K)) : Set K)) := by
  ext k
  constructor
  · rintro ⟨g, hg, hgk⟩
    exact ⟨(g : G), hg, by
      exact (normalizerEquivMap_apply_coe H e g).trans (congrArg Subtype.val hgk)⟩
  · rintro ⟨g, hg, hgk⟩
    refine ⟨⟨g, _root_.Subgroup.le_normalizer hg⟩, hg, ?_⟩
    ext
    exact hgk

/-- A group isomorphism induces an isomorphism on normalizer quotients. -/
noncomputable abbrev normalizerQuotientEquivMap (H : Subgroup G) (e : G ≃* K) :
    normalizerQuotient H ≃*
      normalizerQuotient (H.map (e : G →* K)) :=
  QuotientGroup.congr
    (H.subgroupOf (_root_.Subgroup.normalizer (H : Set G)))
    ((H.map (e : G →* K)).subgroupOf
      (_root_.Subgroup.normalizer ((H.map (e : G →* K)) : Set K)))
    (normalizerEquivMap H e) (subgroupOf_map_normalizerEquivMap H e)

/-- The induced equivalence on normalizer quotients sends a representative to the image
representative. -/
lemma normalizerQuotientEquivMap_mk (H : Subgroup G) (e : G ≃* K)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientEquivMap H e (normalizerQuotientMk H g) =
      normalizerQuotientMk (H.map (e : G →* K))
        (normalizerEquivMap H e g) :=
  rfl

/-- The inverse induced equivalence sends a target representative to the inverse-image
representative. -/
lemma normalizerQuotientEquivMap_symm_mk (H : Subgroup G) (e : G ≃* K)
    (k : _root_.Subgroup.normalizer ((H.map (e : G →* K)) : Set K)) :
    (normalizerQuotientEquivMap H e).symm (normalizerQuotientMk (H.map (e : G →* K)) k) =
      normalizerQuotientMk H ((normalizerEquivMap H e).symm k) :=
  rfl

/-- After identifying `H.map (MulEquiv.refl G)` with `H`, identity transport on normalizer
quotients fixes representatives. -/
lemma normalizerQuotientEquivMap_refl_mk (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientEquivMap H (MulEquiv.refl G) (normalizerQuotientMk H g) =
      normalizerQuotientMk (H.map ((MulEquiv.refl G : G ≃* G) : G →* G))
        ⟨(g : G), by simp [g.2]⟩ := by
  rw [normalizerQuotientEquivMap_mk]
  rfl

/-- Composing two normalizer-quotient transports sends representatives through the two
successive normalizer transports. -/
lemma normalizerQuotientEquivMap_trans_mk (H : Subgroup G) (e : G ≃* K) (f : K ≃* L)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientEquivMap (H.map (e : G →* K)) f
        (normalizerQuotientEquivMap H e (normalizerQuotientMk H g)) =
      normalizerQuotientMk ((H.map (e : G →* K)).map (f : K →* L))
        (normalizerEquivMap (H.map (e : G →* K)) f (normalizerEquivMap H e g)) := by
  rw [normalizerQuotientEquivMap_mk, normalizerQuotientEquivMap_mk]

/-- After the subgroup equality `H.map id = H`, identity transport on normalizer quotients is
the canonical identity on representatives. -/
lemma normalizerQuotientEquivMap_refl_mk_congr (H : Subgroup G)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientCongr
        (by rw [MulEquiv.coe_monoidHom_refl, _root_.Subgroup.map_id] :
          H.map ((MulEquiv.refl G : G ≃* G) : G →* G) = H)
      (normalizerQuotientEquivMap H (MulEquiv.refl G) (normalizerQuotientMk H g)) =
      normalizerQuotientMk H g := by
  rw [normalizerQuotientEquivMap_mk]
  rfl

/-- After identifying the twice-mapped subgroup with the subgroup mapped by `e.trans f`,
composing normalizer-quotient transports agrees with transport by the composite isomorphism on
representatives. -/
lemma normalizerQuotientEquivMap_trans_mk_congr (H : Subgroup G) (e : G ≃* K) (f : K ≃* L)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientCongr
        (by rw [_root_.Subgroup.map_map, ← MulEquiv.coe_monoidHom_trans] :
          (H.map (e : G →* K)).map (f : K →* L) =
            H.map ((e.trans f : G ≃* L) : G →* L))
      (normalizerQuotientEquivMap (H.map (e : G →* K)) f
        (normalizerQuotientEquivMap H e (normalizerQuotientMk H g))) =
      normalizerQuotientEquivMap H (e.trans f) (normalizerQuotientMk H g) := by
  rw [normalizerQuotientEquivMap_mk, normalizerQuotientEquivMap_mk]
  rfl

/-- Transporting a representative of `H.map e` along `e.symm` gives the stated inverse-image
representative in `(H.map e).map e.symm`. -/
@[simp]
lemma normalizerQuotientEquivMap_symm_mk' (H : Subgroup G) (e : G ≃* K)
    (k : _root_.Subgroup.normalizer ((H.map (e : G →* K)) : Set K)) :
    normalizerQuotientEquivMap (H.map (e : G →* K)) e.symm
        (normalizerQuotientMk (H.map (e : G →* K)) k) =
      normalizerQuotientMk ((H.map (e : G →* K)).map (e.symm : K →* G))
        (normalizerEquivMap (H.map (e : G →* K)) e.symm k) := by
  rw [normalizerQuotientEquivMap_mk]

/-- On representatives, `normalizerQuotientEquivMap` applies the original group
isomorphism. -/
lemma normalizerQuotientEquivMap_mk_coe (H : Subgroup G) (e : G ≃* K)
    (g : _root_.Subgroup.normalizer (H : Set G)) :
    normalizerQuotientEquivMap H e (normalizerQuotientMk H g) =
      normalizerQuotientMk (H.map (e : G →* K))
        ⟨e (g : G), by
          rw [← normalizerEquivMap_apply_coe H e g]
          exact (normalizerEquivMap H e g).2⟩ := by
  rw [normalizerQuotientEquivMap_mk]
  rfl

end Subgroup

end TauCeti
