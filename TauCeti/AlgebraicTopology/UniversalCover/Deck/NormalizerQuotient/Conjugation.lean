/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Group.NormalizerQuotient.Conjugation
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Conjugation

/-!
# Conjugating deck normalizer quotients

An isomorphism of covers over a common base identifies deck groups by conjugation. This file
records the induced identification on the normalizer quotients `N(H) / H` of deck subgroups.
Those quotients are the algebraic groups appearing in the universal-covers roadmap as deck
groups of covers attached to subgroups.

## Main declarations

* `TauCeti.Deck.normalizerQuotientConjEquiv`: conjugation along an over-base homeomorphism
  identifies `N(H) / H` with `N(conj(H)) / conj(H)`.
* Representative formulas for the forward and inverse maps, including composition
  compatibility on representatives.

## References

This supplies a basepoint-change and cover-isomorphism bookkeeping prerequisite for
`TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8: pointed connected covers
correspond to subgroups, unpointed connected covers correspond to conjugacy classes of
subgroups, and the deck group attached to `H` is `N(H) / H`.
-/

public section

namespace TauCeti

namespace Deck

variable {E F B : Type*} [TopologicalSpace E] [TopologicalSpace F]
  {p : E → B} {q : F → B}

/-- Conjugating an over-base homeomorphism identifies the normalizer quotient of a deck
subgroup with the normalizer quotient of the conjugated subgroup. -/
noncomputable abbrev normalizerQuotientConjEquiv (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p)) :
    Subgroup.normalizerQuotient H ≃*
      Subgroup.normalizerQuotient
        (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) :=
  Subgroup.normalizerQuotientEquivMap H (conjMulEquiv h hpq)

/-- On normalizer representatives, the deck normalizer-quotient conjugation equivalence is
induced by conjugating deck transformations. -/
lemma normalizerQuotientConjEquiv_mk (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    normalizerQuotientConjEquiv h hpq H (Subgroup.normalizerQuotientMk H φ) =
      Subgroup.normalizerQuotientMk
        (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
        (Subgroup.normalizerEquivMap H (conjMulEquiv h hpq) φ) :=
  Subgroup.normalizerQuotientEquivMap_mk H (conjMulEquiv h hpq) φ

/-- After the subgroup equality induced by identity conjugation, conjugating the normalizer
quotient by the identity over-base homeomorphism is the canonical identity on representatives. -/
lemma normalizerQuotientConjEquiv_refl_mk_congr (H : Subgroup (Deck p))
    (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    Subgroup.normalizerQuotientCongr (subgroup_map_conj_refl (p := p) H)
      (normalizerQuotientConjEquiv (Homeomorph.refl E) (p := p) (q := p)
        (fun e => by rfl : ∀ e, p ((Homeomorph.refl E) e) = p e) H
        (Subgroup.normalizerQuotientMk H φ)) =
      Subgroup.normalizerQuotientMk H φ := by
  rw [normalizerQuotientConjEquiv_mk, Subgroup.normalizerQuotientCongr_mk]
  congr 1
  ext x
  -- The subgroup congruence proof still mentions the opaque identity `conjMulEquiv`, so after
  -- the quotient congruence the remaining representative equality has to be exposed pointwise.
  change ((conjMulEquiv (Homeomorph.refl E) (p := p) (q := p)
    (fun e => by rfl : ∀ e, p ((Homeomorph.refl E) e) = p e)
    (φ : Deck p) : Deck p).1 x) = (φ : Deck p).1 x
  simp

/-- The inverse deck normalizer-quotient conjugation equivalence is induced by inverse
conjugation of deck transformations. -/
lemma normalizerQuotientConjEquiv_symm_mk (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p)) (ψ : _root_.Subgroup.normalizer
      ((H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) :
        Set (Deck q))) :
    (normalizerQuotientConjEquiv h hpq H).symm
        (Subgroup.normalizerQuotientMk
          (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) ψ) =
      Subgroup.normalizerQuotientMk H
        ((Subgroup.normalizerEquivMap H (conjMulEquiv h hpq)).symm ψ) :=
    Subgroup.normalizerQuotientEquivMap_symm_mk H (conjMulEquiv h hpq) ψ

/-- Composing two deck normalizer-quotient conjugation equivalences sends representatives through
the two successive conjugation transports. -/
lemma normalizerQuotientConjEquiv_trans_mk {G : Type*} [TopologicalSpace G] {r : G → B}
    (h : E ≃ₜ F) (k : F ≃ₜ G) (hpq : ∀ e, q (h e) = p e) (hqr : ∀ f, r (k f) = q f)
    (H : Subgroup (Deck p)) (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    normalizerQuotientConjEquiv k hqr
        (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
        (normalizerQuotientConjEquiv h hpq H (Subgroup.normalizerQuotientMk H φ)) =
      Subgroup.normalizerQuotientMk
        ((H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)).map
          ((conjMulEquiv k hqr : Deck q ≃* Deck r) : Deck q →* Deck r))
        (Subgroup.normalizerEquivMap
          (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
          (conjMulEquiv k hqr)
          (Subgroup.normalizerEquivMap H (conjMulEquiv h hpq) φ)) := by
  exact Subgroup.normalizerQuotientEquivMap_trans_mk H (conjMulEquiv h hpq)
    (conjMulEquiv k hqr) φ

/-- After identifying the twice-conjugated subgroup with the subgroup conjugated by the
composite over-base homeomorphism, composing deck normalizer-quotient conjugation equivalences
agrees with conjugation by the composite on representatives. -/
lemma normalizerQuotientConjEquiv_trans_mk_congr {G : Type*} [TopologicalSpace G] {r : G → B}
    (h : E ≃ₜ F) (k : F ≃ₜ G) (hpq : ∀ e, q (h e) = p e) (hqr : ∀ f, r (k f) = q f)
    (H : Subgroup (Deck p)) (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    Subgroup.normalizerQuotientCongr (subgroup_map_conj_trans h k hpq hqr H)
      (normalizerQuotientConjEquiv k hqr
        (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
        (normalizerQuotientConjEquiv h hpq H (Subgroup.normalizerQuotientMk H φ))) =
      normalizerQuotientConjEquiv (h.trans k)
        (fun e => by rw [Homeomorph.trans_apply, hqr, hpq]) H
        (Subgroup.normalizerQuotientMk H φ) := by
  rw [normalizerQuotientConjEquiv_trans_mk, normalizerQuotientConjEquiv_mk,
    Subgroup.normalizerQuotientCongr_mk]
  congr 1
  ext x
  -- The quotient and subgroup congruences reduce the remaining goal to pointwise equality of
  -- the two deck conjugation representatives, where `conjMulEquivTrans` is definitional.
  change (((conjMulEquiv k hqr) ((conjMulEquiv h hpq) (φ : Deck p)) : Deck r).1 x) =
    ((conjMulEquiv (h.trans k) (fun e => by rw [Homeomorph.trans_apply, hqr, hpq])
      (φ : Deck p) : Deck r).1 x)
  simp [conjMulEquiv_apply_coe]

/-- Inverse-conjugating a representative of the `h`-conjugated subgroup quotient gives the
stated representative in the twice-mapped subgroup. -/
lemma normalizerQuotientConjEquiv_symm_mk' (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p)) (ψ : _root_.Subgroup.normalizer
      ((H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) :
        Set (Deck q))) :
    normalizerQuotientConjEquiv h.symm (map_symm_eq_of_map_eq h hpq)
        (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
        (Subgroup.normalizerQuotientMk
          (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) ψ) =
      Subgroup.normalizerQuotientMk
        ((H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)).map
          ((conjMulEquiv h.symm (map_symm_eq_of_map_eq h hpq) : Deck q ≃* Deck p) :
            Deck q →* Deck p))
        (Subgroup.normalizerEquivMap
          (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
          (conjMulEquiv h.symm (map_symm_eq_of_map_eq h hpq)) ψ) := by
  exact Subgroup.normalizerQuotientEquivMap_mk
    (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
    (conjMulEquiv h.symm (map_symm_eq_of_map_eq h hpq)) ψ

/-- On underlying deck transformations, the normalizer representative in the target quotient
is obtained by conjugation. -/
lemma normalizerQuotientConjEquiv_mk_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p)) (φ : _root_.Subgroup.normalizer (H : Set (Deck p))) :
    normalizerQuotientConjEquiv h hpq H (Subgroup.normalizerQuotientMk H φ) =
      Subgroup.normalizerQuotientMk
        (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q))
        ⟨conjMulEquiv h hpq (φ : Deck p), by
          rw [← Subgroup.normalizerEquivMap_apply_coe H (conjMulEquiv h hpq) φ]
          exact (Subgroup.normalizerEquivMap H (conjMulEquiv h hpq) φ).2⟩ := by
  exact Subgroup.normalizerQuotientEquivMap_mk_coe H (conjMulEquiv h hpq) φ

/-- On representatives, inverse transport of the deck normalizer quotient applies inverse
conjugation. -/
lemma normalizerQuotientConjEquiv_symm_mk_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (H : Subgroup (Deck p)) (ψ : _root_.Subgroup.normalizer
      ((H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) :
        Set (Deck q))) :
    (normalizerQuotientConjEquiv h hpq H).symm
        (Subgroup.normalizerQuotientMk
          (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)) ψ) =
      Subgroup.normalizerQuotientMk H
        ⟨(conjMulEquiv h hpq).symm (ψ : Deck q), by
          rw [← Subgroup.normalizerEquivMap_symm_apply_coe H (conjMulEquiv h hpq) ψ]
          exact ((Subgroup.normalizerEquivMap H (conjMulEquiv h hpq)).symm ψ).2⟩ := by
  rw [normalizerQuotientConjEquiv_symm_mk]
  rfl

end Deck

end TauCeti
