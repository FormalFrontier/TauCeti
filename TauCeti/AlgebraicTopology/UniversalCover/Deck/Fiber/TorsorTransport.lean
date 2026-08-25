/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular.Torsor

/-!
# Transporting deck fibre torsors

An over-base homeomorphism between two covers identifies their deck groups by conjugation
and their corresponding fibres by `Deck.fiberMap`. This file records that these two
identifications are compatible with the torsor structures on fibres.

The main statement is first proved for the local situation of a preconnected covering whose
chosen fibre has a free transitive deck action. The regular-cover wrappers then specialize
it using `Deck.IsRegular`, which is the form used in the universal-covers roadmap when
pointed covers are compared up to changing representatives over the same base.

## Main declarations

* `TauCeti.Deck.fiberMap_sdiv_eq_conjMulEquiv_of_pretransitive`: fibre transport carries
  torsor division to conjugation of the corresponding deck transformation.
* `TauCeti.Deck.fiberMap_sdiv_eq_conjMulEquiv`: the regular-cover specialization.
* `TauCeti.Deck.deckEquivFiber_fiberMap`: transport is compatible with the
  deck-to-fibre equivalence of a regular cover.

## References

This supplies a bookkeeping prerequisite for `TauCetiRoadmap/UniversalCovers/README.md`,
Stage 2: the pointed and unpointed cover correspondences require changing the chosen lift in
a fibre while transporting deck actions along isomorphisms of covers.
-/

public section

namespace TauCeti

namespace Deck

variable {E F B : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  {p : E → B} {q : F → B} {b : B}

omit [TopologicalSpace B] in
/-- Fibre transport carries a pretransitive deck action on the source fibre to a pretransitive
deck action on the target fibre. -/
lemma isPretransitive_fiberMap (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})] :
    MulAction.IsPretransitive (Deck q) (q ⁻¹' {b}) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := (fiberMap h hpq b).surjective x
  obtain ⟨y', rfl⟩ := (fiberMap h hpq b).surjective y
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Deck p) x' y'
  exact ⟨conjMulEquiv h hpq g, (fiberMap_smul h hpq g x').symm⟩

omit [TopologicalSpace B] in
/-- Fibre transport carries surjectivity of evaluation at a source fibre point to surjectivity
of evaluation at the transported target fibre point. -/
lemma surjective_smul_fiberMap (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (e : p ⁻¹' {b}) (hsurj : Function.Surjective fun φ : Deck p => φ • e) :
    Function.Surjective fun ψ : Deck q => ψ • fiberMap h hpq b e := by
  intro f
  obtain ⟨e', rfl⟩ := (fiberMap h hpq b).surjective f
  obtain ⟨φ, rfl⟩ := hsurj e'
  exact ⟨conjMulEquiv h hpq φ, (fiberMap_smul h hpq φ e).symm⟩

/-- The inverse of the local deck-to-fibre equivalence is compatible with fibre transport:
transport the target fibre point first, or compute the source deck transformation first and
then conjugate it. -/
@[simp]
lemma deckEquivFiberOfSurjective_symm_fiberMap [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (e e' : p ⁻¹' {b})
    (hsurj : Function.Surjective fun φ : Deck p => φ • e) :
    letI : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
    (deckEquivFiberOfSurjective hq (fiberMap h hpq b e)
          (surjective_smul_fiberMap h hpq e hsurj)).symm
        (fiberMap h hpq b e') =
      conjMulEquiv h hpq ((deckEquivFiberOfSurjective hp e hsurj).symm e') := by
  let : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
  apply (deckEquivFiberOfSurjective hq (fiberMap h hpq b e)
    (surjective_smul_fiberMap h hpq e hsurj)).injective
  rw [Equiv.apply_symm_apply, deckEquivFiberOfSurjective_apply, ← fiberMap_smul,
    deckEquivFiberOfSurjective_symm_smul]

/-- Fibre transport preserves torsor division, with the deck-group element transported by
conjugation along the over-base homeomorphism.

This is the local pretransitive-fibre form. The regular-cover API below supplies the
nonemptiness and pretransitivity hypotheses from `Deck.IsRegular`. -/
@[simp]
lemma fiberMap_sdiv_eq_conjMulEquiv_of_pretransitive [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    [Nonempty (p ⁻¹' {b})] [MulAction.IsPretransitive (Deck p) (p ⁻¹' {b})]
    (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e₁ e₂ : p ⁻¹' {b}) :
    letI : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
    letI := fiberTorsorOfPretransitive hp b
    letI : Nonempty (q ⁻¹' {b}) := ‹Nonempty (p ⁻¹' {b})›.map (fiberMap h hpq b)
    letI : MulAction.IsPretransitive (Deck q) (q ⁻¹' {b}) := isPretransitive_fiberMap h hpq
    letI := fiberTorsorOfPretransitive hq b
    (fiberMap h hpq b e₁ /ₛ fiberMap h hpq b e₂ : Deck q) =
      conjMulEquiv h hpq (e₁ /ₛ e₂ : Deck p) := by
  let : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
  let := fiberTorsorOfPretransitive hp b
  let : Nonempty (q ⁻¹' {b}) := ‹Nonempty (p ⁻¹' {b})›.map (fiberMap h hpq b)
  let : MulAction.IsPretransitive (Deck q) (q ⁻¹' {b}) := isPretransitive_fiberMap h hpq
  let := fiberTorsorOfPretransitive hq b
  rw [← deckEquivFiberOfSurjective_symm_eq_sdiv hq,
    ← deckEquivFiberOfSurjective_symm_eq_sdiv hp]
  exact deckEquivFiberOfSurjective_symm_fiberMap hp hq h hpq e₂ e₁
    (MulAction.surjective_smul (Deck p) e₂)

/-- The local deck-to-fibre equivalence commutes with transport of deck transformations
and fibre points along an over-base homeomorphism. -/
lemma deckEquivFiberOfSurjective_fiberMap [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b})
    (hsurj : Function.Surjective fun φ : Deck p => φ • e) (φ : Deck p) :
    letI : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
    deckEquivFiberOfSurjective hq (fiberMap h hpq b e)
        (surjective_smul_fiberMap h hpq e hsurj) (conjMulEquiv h hpq φ) =
      fiberMap h hpq b (deckEquivFiberOfSurjective hp e hsurj φ) := by
  let : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
  rw [deckEquivFiberOfSurjective_apply, deckEquivFiberOfSurjective_apply, fiberMap_smul]

/-- On underlying points, local compatibility of `deckEquivFiberOfSurjective` with fibre
transport says that conjugating a deck transformation and then evaluating on the transported
fibre point is the same as transporting the original evaluation. -/
lemma deckEquivFiberOfSurjective_fiberMap_coe [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b})
    (hsurj : Function.Surjective fun φ : Deck p => φ • e) (φ : Deck p) :
    letI : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
    (deckEquivFiberOfSurjective hq (fiberMap h hpq b e)
        (surjective_smul_fiberMap h hpq e hsurj) (conjMulEquiv h hpq φ) : F) =
      h (φ.1 e.1) := by
  let : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
  rw [deckEquivFiberOfSurjective_fiberMap hp hq h hpq e hsurj φ,
    fiberMap_apply_coe, deckEquivFiberOfSurjective_apply_coe]

/-- The inverse of the regular deck-to-fibre equivalence is compatible with fibre transport:
transport the target fibre point first, or compute the source deck transformation first and
then conjugate it. -/
lemma deckEquivFiber_symm_fiberMap [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (hreg : IsRegular p)
    (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e e' : p ⁻¹' {b}) :
    letI : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
    (deckEquivFiber hq (hreg.conj h hpq) (fiberMap h hpq b e)).symm
        (fiberMap h hpq b e') =
      conjMulEquiv h hpq ((deckEquivFiber hp hreg e).symm e') := by
  let : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
  let hregq := hreg.conj h hpq
  let := hreg.fiber_isPretransitive b
  let := hregq.fiber_isPretransitive b
  exact deckEquivFiberOfSurjective_symm_fiberMap hp hq h hpq e e'
    (MulAction.surjective_smul (Deck p) e)

/-- The regular deck-to-fibre equivalence commutes with transport of deck transformations
and fibre points along an over-base homeomorphism. -/
lemma deckEquivFiber_fiberMap [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (hreg : IsRegular p)
    (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b}) (φ : Deck p) :
    letI : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
    deckEquivFiber hq (hreg.conj h hpq) (fiberMap h hpq b e) (conjMulEquiv h hpq φ) =
      fiberMap h hpq b (deckEquivFiber hp hreg e φ) := by
  let : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
  let hregq := hreg.conj h hpq
  let := hreg.fiber_isPretransitive b
  let := hregq.fiber_isPretransitive b
  exact deckEquivFiberOfSurjective_fiberMap hp hq h hpq e
    (MulAction.surjective_smul (Deck p) e) φ

/-- On underlying points, the compatibility of `deckEquivFiber` with fibre transport says
that conjugating a deck transformation and then evaluating on the transported fibre point is
the same as transporting the original evaluation. -/
lemma deckEquivFiber_fiberMap_coe [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (hreg : IsRegular p)
    (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b}) (φ : Deck p) :
    letI : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
    (deckEquivFiber hq (hreg.conj h hpq) (fiberMap h hpq b e)
        (conjMulEquiv h hpq φ) : F) =
      h (φ.1 e.1) := by
  let : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
  rw [deckEquivFiber_fiberMap hp hq hreg h hpq e φ, fiberMap_apply_coe,
    deckEquivFiber_apply_coe]

/-- For regular preconnected covers, fibre transport preserves torsor division, with the
deck transformation conjugated to the target deck group. -/
@[simp]
lemma fiberMap_sdiv_eq_conjMulEquiv [PreconnectedSpace E]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (hreg : IsRegular p)
    (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e₁ e₂ : p ⁻¹' {b}) :
    letI : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
    letI := fiberTorsor hp hreg b
    letI := fiberTorsor hq (hreg.conj h hpq) b
    (fiberMap h hpq b e₁ /ₛ fiberMap h hpq b e₂ : Deck q) =
      conjMulEquiv h hpq (e₁ /ₛ e₂ : Deck p) := by
  let : PreconnectedSpace F := h.surjective.denseRange.preconnectedSpace h.continuous
  rw [fiber_sdiv_eq_deckEquivFiber_symm hq (hreg.conj h hpq),
    fiber_sdiv_eq_deckEquivFiber_symm hp hreg]
  exact deckEquivFiber_symm_fiberMap hp hq hreg h hpq e₂ e₁

end Deck

end TauCeti
