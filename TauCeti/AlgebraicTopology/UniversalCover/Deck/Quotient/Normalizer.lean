/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Group
public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.ActingGroup
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# The deck group of an intermediate quotient is a normalizer quotient

Let `p : E → X` be a quotient covering map for a group `Γ` acting on `E`, let `H ≤ Γ`, and let
`q : E → F` present `F` as the quotient of `E` by `H`, so that `p` factors as `r ∘ q` for a
covering map `r : F → X`. This file computes the deck transformation group of the intermediate
covering `r`:

  `Deck r ≃* N(H) ⧸ H`,

where `N(H)` is the normalizer of `H` in `Γ`. Taking `H = ⊥` recovers
`TauCeti.Deck.IsQuotientCoveringMap.deckMulEquiv`, which identifies `Deck p` with `Γ` itself.

Only a normalizer element descends to the quotient as a deck transformation: translation by
`γ` respects the `H`-orbit relation, so descends as a map, exactly when `γ H γ⁻¹ ⊆ H`, while
the descended map is invertible, hence a homeomorphism, exactly when `γ H γ⁻¹ = H`, that is,
when `γ` normalizes `H`.

Conversely every deck transformation of `r` arises this way, by uniqueness of lifts. A deck
transformation `φ` of `r`, precomposed with `q`, and translation by a suitable `γ` followed by
`q`, are two lifts of `p` through `r` which agree at one point of the preconnected space `E`,
hence agree everywhere; comparing the translates of a single point then forces `γ` to
normalize `H`.

## Main declarations

* `TauCeti.Deck.IsQuotientCoveringMap.normalizerMap`: translation by a normalizer element,
  descended to the orbit quotient.
* `TauCeti.Deck.IsQuotientCoveringMap.normalizerDeckHom`: the resulting homomorphism from the
  normalizer to `Deck r`.
* `TauCeti.Deck.IsQuotientCoveringMap.ker_normalizerDeckHom`: its kernel is `H`.
* `TauCeti.Deck.IsQuotientCoveringMap.normalizerDeckHom_surjective`: it is surjective when `E`
  is preconnected and `r` is a covering map.
* `TauCeti.Deck.IsQuotientCoveringMap.normalizerQuotientDeckMulEquiv`: **the deck group of `r`
  is `N(H) ⧸ H`.**
* `TauCeti.Deck.IsQuotientCoveringMap.quotientDeckMulEquivOfNormal`: for normal `H` this reads
  `Deck r ≃* Γ ⧸ H`.

## References

This supplies the deck-group half of Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`: the cover attached to `H ≤ π₁(X, x₀)` has deck
group `N(H)/H`, and `π₁(X, x₀)/H` when `H` is normal. The quotient-covering-map interface it
consumes (`Mathlib/Topology/Covering/Quotient.lean`) is due to Junyan Xu, and uniqueness of
lifts, `IsCoveringMap.eq_of_comp_eq` in `Mathlib/Topology/Covering/Basic.lean`, is due to
Thomas Browning after Hatcher, *Algebraic Topology*, Proposition 1.34.
-/

public section
noncomputable section

namespace TauCeti

namespace Deck

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
variable {Γ : Type*} [Group Γ] [MulAction Γ E]
variable {p : E → X} {q : E → F} {r : F → X} {H : Subgroup Γ}

namespace IsQuotientCoveringMap

section Descend

variable (hq : IsQuotientCoveringMap q H)
include hq

/-- Translation by an element of the normalizer of `H`, descended to the quotient of `E` by the
`H`-action. It is well defined because `γ H γ⁻¹ = H`. -/
def normalizerMap (γ : _root_.Subgroup.normalizer (H : Set Γ)) (y : F) : F :=
  q ((γ : Γ) • Function.surjInv hq.surjective y)

/-- The descended translation sends the class of `e` to the class of `γ • e`. -/
@[simp]
theorem normalizerMap_apply (γ : _root_.Subgroup.normalizer (H : Set Γ)) (e : E) :
    normalizerMap hq γ (q e) = q ((γ : Γ) • e) := by
  obtain ⟨h, hh⟩ :=
    hq.apply_eq_iff_mem_orbit.mp (Function.surjInv_eq hq.surjective (q e))
  have hsurj : Function.surjInv hq.surjective (q e) = (h : Γ) • e := hh.symm
  have hconj : (γ : Γ) * (h : Γ) * (γ : Γ)⁻¹ ∈ H :=
    (_root_.Subgroup.mem_normalizer_iff.mp γ.2 (h : Γ)).mp h.2
  have hstep : (γ : Γ) • ((h : Γ) • e) = ((⟨_, hconj⟩ : H) : Γ) • ((γ : Γ) • e) := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    group
  rw [normalizerMap, hsurj, hstep]
  exact hq.map_smul (⟨_, hconj⟩ : H)

/-- The identity of the normalizer descends to the identity. -/
@[simp]
theorem normalizerMap_one (y : F) : normalizerMap hq 1 y = y := by
  obtain ⟨e, rfl⟩ := hq.surjective y
  rw [normalizerMap_apply]
  simp

/-- Descending translations is multiplicative, the right factor acting first. -/
@[simp]
theorem normalizerMap_mul (γ γ' : _root_.Subgroup.normalizer (H : Set Γ)) (y : F) :
    normalizerMap hq (γ * γ') y = normalizerMap hq γ (normalizerMap hq γ' y) := by
  obtain ⟨e, rfl⟩ := hq.surjective y
  rw [normalizerMap_apply, normalizerMap_apply, normalizerMap_apply, Subgroup.coe_mul, mul_smul]

variable [ContinuousConstSMul Γ E]

/-- The descended translation is continuous, because `q` is a quotient map. -/
theorem continuous_normalizerMap (γ : _root_.Subgroup.normalizer (H : Set Γ)) :
    Continuous (normalizerMap hq γ) := by
  rw [hq.toIsQuotientMap.continuous_iff]
  have h : normalizerMap hq γ ∘ q = fun e => q ((γ : Γ) • e) :=
    funext fun e => normalizerMap_apply hq γ e
  rw [h]
  exact hq.isCoveringMap.continuous.comp (continuous_const_smul _)

/-- Translation by a normalizer element, as a homeomorphism of the orbit quotient. -/
def normalizerHomeomorph (γ : _root_.Subgroup.normalizer (H : Set Γ)) : F ≃ₜ F where
  toFun := normalizerMap hq γ
  invFun := normalizerMap hq γ⁻¹
  left_inv y := by rw [← normalizerMap_mul, inv_mul_cancel, normalizerMap_one]
  right_inv y := by rw [← normalizerMap_mul, mul_inv_cancel, normalizerMap_one]
  continuous_toFun := continuous_normalizerMap hq γ
  continuous_invFun := continuous_normalizerMap hq γ⁻¹

@[simp]
theorem normalizerHomeomorph_apply (γ : _root_.Subgroup.normalizer (H : Set Γ)) (e : E) :
    normalizerHomeomorph hq γ (q e) = q ((γ : Γ) • e) :=
  normalizerMap_apply hq γ e

/-- The inverse of the descended translation is translation by the inverse. -/
@[simp]
theorem normalizerHomeomorph_symm_apply (γ : _root_.Subgroup.normalizer (H : Set Γ)) (e : E) :
    (normalizerHomeomorph hq γ).symm (q e) = q ((γ : Γ)⁻¹ • e) := by
  rw [Homeomorph.symm_apply_eq, normalizerHomeomorph_apply, smul_inv_smul]

end Descend

section DeckHom

variable (hp : IsQuotientCoveringMap p Γ) (hq : IsQuotientCoveringMap q H) (hr : r ∘ q = p)
include hp hq hr

/-- Translation by an element normalizing `H`, as a homomorphism from the normalizer to the
deck transformation group of the intermediate covering `r`. -/
def normalizerDeckHom : _root_.Subgroup.normalizer (H : Set Γ) →* Deck r :=
  letI := hp.toContinuousConstSMul
  { toFun := fun γ => ⟨normalizerHomeomorph hq γ, by
      intro y
      obtain ⟨e, rfl⟩ := hq.surjective y
      have hrq : ∀ e' : E, r (q e') = p e' := fun e' => congrFun hr e'
      rw [normalizerHomeomorph_apply, hrq, hrq, hp.map_smul]⟩
    map_one' := Subtype.ext (Homeomorph.ext (normalizerMap_one hq))
    map_mul' := fun γ γ' => Subtype.ext (Homeomorph.ext (normalizerMap_mul hq γ γ')) }

/-- On points, the deck transformation attached to a normalizer element is the descent of
translation by that element. -/
@[simp]
theorem normalizerDeckHom_apply (γ : _root_.Subgroup.normalizer (H : Set Γ)) (e : E) :
    (normalizerDeckHom hp hq hr γ).1 (q e) = q ((γ : Γ) • e) :=
  normalizerMap_apply hq γ e

/-- The inverse of the deck transformation attached to a normalizer element is the descent of
translation by the inverse element. -/
@[simp]
theorem normalizerDeckHom_symm_apply (γ : _root_.Subgroup.normalizer (H : Set Γ)) (e : E) :
    (normalizerDeckHom hp hq hr γ).1.symm (q e) = q ((γ : Γ)⁻¹ • e) := by
  rw [Homeomorph.symm_apply_eq, normalizerDeckHom_apply, smul_inv_smul]

/-- The kernel of the normalizer-to-deck homomorphism is `H`: a translation descends to the
identity exactly when it is an `H`-translation, because the `Γ`-action is free. -/
theorem ker_normalizerDeckHom [Nonempty E] :
    (normalizerDeckHom hp hq hr).ker
      = H.subgroupOf (_root_.Subgroup.normalizer (H : Set Γ)) := by
  have := hp.isCancelSMul
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hγ
    obtain ⟨e⟩ := ‹Nonempty E›
    have h1 : q ((γ : Γ) • e) = q e := by
      rw [← normalizerDeckHom_apply hp hq hr γ e, hγ]
      rfl
    obtain ⟨h, hh⟩ := hq.apply_eq_iff_mem_orbit.mp h1
    have hcoe : (h : Γ) = (γ : Γ) := IsCancelSMul.right_cancel _ _ e hh
    exact hcoe ▸ h.2
  · intro hγ
    refine Subtype.ext (Homeomorph.ext fun y => ?_)
    obtain ⟨e, rfl⟩ := hq.surjective y
    rw [normalizerDeckHom_apply]
    exact hq.map_smul (⟨(γ : Γ), hγ⟩ : H)

omit hr in
/-- If translating a fixed point by `γ` is insensitive to an `H`-translation first, then `γ`
conjugates `H` into itself. -/
private theorem conj_mem_of_smul_eq {γ : Γ} {e₀ : E}
    (hγ : ∀ h ∈ H, q ((γ * h) • e₀) = q (γ • e₀)) {h : Γ} (hh : h ∈ H) :
    γ * h * γ⁻¹ ∈ H := by
  have := hp.isCancelSMul
  obtain ⟨h', hh'⟩ := hq.apply_eq_iff_mem_orbit.mp (hγ h hh)
  have hcancel : (h' : Γ) * γ = γ * h := by
    refine IsCancelSMul.right_cancel _ _ e₀ ?_
    rw [mul_smul]
    exact hh'
  have hrw : γ * h * γ⁻¹ = (h' : Γ) := by rw [← hcancel, mul_inv_cancel_right]
  exact hrw ▸ h'.2

/-- Every deck transformation of the intermediate covering is the descent of a translation by
a normalizer element. -/
theorem normalizerDeckHom_surjective [PreconnectedSpace E] (hrc : IsCoveringMap r) :
    Function.Surjective (normalizerDeckHom hp hq hr) := by
  have := hp.toContinuousConstSMul
  intro φ
  rcases isEmpty_or_nonempty E with hE | hne
  · -- `q` is surjective, so `F` is empty too and every deck transformation is the identity.
    exact ⟨1, Subtype.ext (Homeomorph.ext fun y => by
      obtain ⟨e, rfl⟩ := hq.surjective y
      exact (hE.false e).elim)⟩
  obtain ⟨e₀⟩ := hne
  obtain ⟨e₁, he₁⟩ := hq.surjective (φ.1 (q e₀))
  have hrq : ∀ e : E, r (q e) = p e := fun e => congrFun hr e
  have hpe : p e₁ = p e₀ := by rw [← hrq e₁, ← hrq e₀, he₁, Deck.map_proj φ (q e₀)]
  obtain ⟨γ, hγ⟩ := hp.apply_eq_iff_mem_orbit.mp hpe
  -- `φ ∘ q` and `q ∘ (γ • ·)` are two lifts of `p` through `r`, agreeing at `e₀`.
  have hkey : ∀ e, φ.1 (q e) = q (γ • e) := by
    refine congrFun (hrc.eq_of_comp_eq (g₁ := fun e => φ.1 (q e)) (g₂ := fun e => q (γ • e))
      (φ.1.continuous.comp hq.isCoveringMap.continuous)
      (hq.isCoveringMap.continuous.comp (continuous_const_smul _)) (funext fun e => ?_) e₀ ?_)
    · rw [Function.comp_apply, Function.comp_apply, Deck.map_proj φ (q e), hrq e, hrq (γ • e),
        hp.map_smul]
    · have hγ' : (γ • e₀ : E) = e₁ := hγ
      rw [hγ', he₁]
  have hkey' : ∀ e, φ.1.symm (q e) = q (γ⁻¹ • e) := fun e => by
    rw [Homeomorph.symm_apply_eq, hkey, smul_inv_smul]
  have hstep : ∀ h ∈ H, q ((γ * h) • e₀) = q (γ • e₀) := by
    intro h hh
    rw [mul_smul, ← hkey, ← hkey]
    exact congrArg φ.1 (hq.map_smul (⟨h, hh⟩ : H))
  have hstep' : ∀ h ∈ H, q ((γ⁻¹ * h) • e₀) = q (γ⁻¹ • e₀) := by
    intro h hh
    rw [mul_smul, ← hkey', ← hkey']
    exact congrArg φ.1.symm (hq.map_smul (⟨h, hh⟩ : H))
  have hmem : γ ∈ _root_.Subgroup.normalizer (H : Set Γ) := by
    rw [_root_.Subgroup.mem_normalizer_iff]
    refine fun h => ⟨fun hh => conj_mem_of_smul_eq hp hq hstep hh, fun hh => ?_⟩
    have hback := conj_mem_of_smul_eq hp hq hstep' hh
    simpa [mul_assoc] using hback
  refine ⟨⟨γ, hmem⟩, Subtype.ext (Homeomorph.ext fun y => ?_)⟩
  obtain ⟨e, rfl⟩ := hq.surjective y
  rw [normalizerDeckHom_apply, ← hkey]

/-- **The deck group of an intermediate covering is the normalizer quotient.** For a quotient
covering map `p : E → X` with preconnected nonempty total space, a subgroup `H` of the acting
group, and the induced covering `r : E / H → X`, translation identifies `N(H) ⧸ H` with
`Deck r`. -/
def normalizerQuotientDeckMulEquiv [PreconnectedSpace E] [Nonempty E] (hrc : IsCoveringMap r) :
    (_root_.Subgroup.normalizer (H : Set Γ)) ⧸
        H.subgroupOf (_root_.Subgroup.normalizer (H : Set Γ)) ≃* Deck r :=
  (QuotientGroup.quotientMulEquivOfEq (ker_normalizerDeckHom hp hq hr).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (normalizerDeckHom hp hq hr)
      (normalizerDeckHom_surjective hp hq hr hrc))

/-- The normalizer-quotient isomorphism sends the class of `γ` to the descent of translation
by `γ`. -/
@[simp]
theorem normalizerQuotientDeckMulEquiv_mk [PreconnectedSpace E] [Nonempty E]
    (hrc : IsCoveringMap r) (γ : _root_.Subgroup.normalizer (H : Set Γ)) :
    normalizerQuotientDeckMulEquiv hp hq hr hrc (QuotientGroup.mk γ) =
      normalizerDeckHom hp hq hr γ := by
  simp [normalizerQuotientDeckMulEquiv, QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

end DeckHom

section Normal

variable (hp : IsQuotientCoveringMap p Γ) (hq : IsQuotientCoveringMap q H) (hr : r ∘ q = p)
variable [H.Normal]
include hp hq hr

omit hp hq hr in
/-- For a normal subgroup, the identity is a homomorphism onto the normalizer. -/
private def toNormalizerOfNormal : Γ →* _root_.Subgroup.normalizer (H : Set Γ) where
  toFun γ := ⟨γ, _root_.Subgroup.subset_normalizer_of_normal (Set.mem_univ γ)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- For a normal subgroup every group element descends, giving a homomorphism from the whole
acting group to the deck group of the intermediate covering. -/
def deckHomOfNormal : Γ →* Deck r :=
  (normalizerDeckHom hp hq hr).comp (toNormalizerOfNormal (H := H))

@[simp]
theorem deckHomOfNormal_apply (γ : Γ) (e : E) :
    (deckHomOfNormal hp hq hr γ).1 (q e) = q (γ • e) :=
  normalizerDeckHom_apply hp hq hr _ e

/-- The inverse of the deck transformation attached to `γ` is the descent of translation by
`γ⁻¹`. -/
@[simp]
theorem deckHomOfNormal_symm_apply (γ : Γ) (e : E) :
    (deckHomOfNormal hp hq hr γ).1.symm (q e) = q (γ⁻¹ • e) :=
  normalizerDeckHom_symm_apply hp hq hr _ e

/-- **For a normal subgroup, the deck group of the intermediate covering is `Γ ⧸ H`.** This is
the general normalizer-quotient identification, read through the algebraic comparison
`TauCeti.Subgroup.normalizerQuotientEquivQuotientOfNormal` between `N(H) ⧸ H` and `Γ ⧸ H`. -/
def quotientDeckMulEquivOfNormal [PreconnectedSpace E] [Nonempty E] (hrc : IsCoveringMap r) :
    Γ ⧸ H ≃* Deck r :=
  (Subgroup.normalizerQuotientEquivQuotientOfNormal H).symm.trans
    (normalizerQuotientDeckMulEquiv hp hq hr hrc)

/-- The isomorphism `Γ ⧸ H ≃* Deck r` sends the class of `γ` to the descent of translation
by `γ`. -/
@[simp]
theorem quotientDeckMulEquivOfNormal_mk [PreconnectedSpace E] [Nonempty E]
    (hrc : IsCoveringMap r) (γ : Γ) :
    quotientDeckMulEquivOfNormal hp hq hr hrc (QuotientGroup.mk γ) =
      deckHomOfNormal hp hq hr γ := by
  -- Unwinding both equivalences leaves translation by the same normalizer element `⟨γ, _⟩` on
  -- either side, reached through two different membership proofs.
  simp [quotientDeckMulEquivOfNormal, deckHomOfNormal, toNormalizerOfNormal]
  congr 1

end Normal

end IsQuotientCoveringMap

end Deck

end TauCeti
