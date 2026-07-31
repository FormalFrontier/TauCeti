/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Basic

/-!
# Conjugating deck transformations

An isomorphism of maps over the same base transports deck transformations by conjugation.
This file packages that transport as a multiplicative equivalence of deck groups. It is
basic bookkeeping for the universal-covers roadmap: once covers are organized up to
isomorphism over the base, their deck groups must be identified by conjugating along the
chosen total-space homeomorphism.

## Main definitions

* `TauCeti.Deck.conjMulEquiv`: if `h : E ≃ₜ F` satisfies `q (h e) = p e`, then
  conjugation by `h` gives `Deck p ≃* Deck q`.
* `TauCeti.Deck.conjMulEquivRefl`: the identity over-base homeomorphism induces the
  identity deck-group equivalence.
* `TauCeti.Deck.conjMulEquivTrans`: conjugating along a composite over-base
  homeomorphism is the composite of the conjugation equivalences.

## References

This file supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stage 0.4
(`Deck p` as the deck transformation group), and the later cover-isomorphism bookkeeping in
Stage 2.
-/

public section

namespace TauCeti

namespace Deck

variable {E F G B : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
  {p : E → B} {q : F → B} {r : G → B}

/-- If `h : E ≃ₜ F` lies over the base, then its inverse also lies over the base in the
opposite direction. -/
lemma map_symm_eq_of_map_eq (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (f : F) :
    p (h.symm f) = q f := by
  rw [← hpq (h.symm f), h.apply_symm_apply]

/-- The homeomorphism obtained by conjugating an end-homeomorphism by `h`. -/
private def conjHomeomorph (h : E ≃ₜ F) (φ : E ≃ₜ E) : F ≃ₜ F :=
  (h.symm.trans φ).trans h

/-- Conjugating by the identity homeomorphism leaves an end-homeomorphism unchanged. -/
@[simp]
private lemma conjHomeomorph_refl (φ : E ≃ₜ E) :
    conjHomeomorph (Homeomorph.refl E) φ = φ := by
  ext e
  simp [conjHomeomorph]

/-- Conjugation by a homeomorphism evaluates by `h.symm`, then `φ`, then `h`. -/
@[simp]
private lemma conjHomeomorph_apply (h : E ≃ₜ F) (φ : E ≃ₜ E) (f : F) :
    conjHomeomorph h φ f = h (φ (h.symm f)) := by
  rfl

/-- The inverse of a conjugated homeomorphism is the conjugate of the inverse. -/
@[simp]
private lemma conjHomeomorph_symm (h : E ≃ₜ F) (φ : E ≃ₜ E) :
    (conjHomeomorph h φ).symm = conjHomeomorph h φ.symm := by
  ext f
  simp [conjHomeomorph]

/-- Conjugation sends the identity homeomorphism to the identity homeomorphism. -/
@[simp]
private lemma conjHomeomorph_one (h : E ≃ₜ F) :
    conjHomeomorph h 1 = 1 := by
  ext f
  simp [conjHomeomorph]

/-- Conjugation sends composition of homeomorphisms to composition of the conjugates. -/
@[simp]
private lemma conjHomeomorph_mul (h : E ≃ₜ F) (φ ψ : E ≃ₜ E) :
    conjHomeomorph h (φ * ψ) = conjHomeomorph h φ * conjHomeomorph h ψ := by
  ext f
  simp [conjHomeomorph, Homeomorph.mul_apply]

/-- Conjugating twice is the same as conjugating by the composite homeomorphism. -/
@[simp]
private lemma conjHomeomorph_trans (h : E ≃ₜ F) (k : F ≃ₜ G) (φ : E ≃ₜ E) :
    conjHomeomorph k (conjHomeomorph h φ) = conjHomeomorph (h.trans k) φ := by
  ext g
  simp [conjHomeomorph]

/-- Conjugation by a homeomorphism as a multiplicative equivalence of homeomorphism groups. -/
private def conjHomeomorphMulEquiv (h : E ≃ₜ F) : (E ≃ₜ E) ≃* (F ≃ₜ F) where
  toFun := conjHomeomorph h
  invFun := conjHomeomorph h.symm
  left_inv φ := by
    ext e
    simp [conjHomeomorph]
  right_inv ψ := by
    ext f
    simp [conjHomeomorph]
  map_mul' φ ψ := by
    ext f
    simp [conjHomeomorph, Homeomorph.mul_apply]

/-- Conjugation by an over-base homeomorphism sends deck transformations to deck
transformations. -/
private lemma conjHomeomorph_mem_deck (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (φ : Deck p) :
    conjHomeomorph h φ.1 ∈ Deck q := by
  intro f
  calc
    q (conjHomeomorph h φ.1 f) = q (h (φ.1 (h.symm f))) := rfl
    _ = p (φ.1 (h.symm f)) := hpq _
    _ = p (h.symm f) := map_proj φ _
    _ = q f := map_symm_eq_of_map_eq h hpq f

/-- The image of a deck group under over-base conjugation is the deck group over the target. -/
private lemma map_conjHomeomorphMulEquiv_deck (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) :
    (Deck p).map (conjHomeomorphMulEquiv h : (E ≃ₜ E) →* (F ≃ₜ F)) = Deck q := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact conjHomeomorph_mem_deck h hpq ⟨ψ, hψ⟩
  · intro hφ
    refine ⟨conjHomeomorph h.symm φ, ?_, ?_⟩
    · exact conjHomeomorph_mem_deck h.symm (map_symm_eq_of_map_eq h hpq) ⟨φ, hφ⟩
    · ext f
      simp [conjHomeomorph, conjHomeomorphMulEquiv]

/-- An isomorphism of maps over the same base identifies their deck transformation groups
by conjugation on the total spaces. -/
def conjMulEquiv (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) : Deck p ≃* Deck q :=
  (conjHomeomorphMulEquiv h).subgroupMap (Deck p) |>.trans <|
    MulEquiv.subgroupCongr (map_conjHomeomorphMulEquiv_deck h hpq)

/-- The deck transformation produced by `conjMulEquiv` evaluates by conjugation. -/
@[simp]
lemma conjMulEquiv_apply_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (φ : Deck p) (f : F) :
    ((conjMulEquiv h hpq φ).1 f) = h (φ.1 (h.symm f)) := by
  rfl

/-- The inverse equivalence of `conjMulEquiv` is conjugation by the inverse
homeomorphism. -/
@[simp]
lemma conjMulEquiv_symm_apply_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (ψ : Deck q) (e : E) :
    (((conjMulEquiv h hpq).symm ψ).1 e) = h.symm (ψ.1 (h e)) := by
  rfl

/-- Conjugating deck transformations along the identity over-base homeomorphism gives the
identity deck-group equivalence. -/
@[simp]
lemma conjMulEquivRefl :
    conjMulEquiv (Homeomorph.refl E) (p := p) (q := p) (fun _ => rfl) =
      MulEquiv.refl (Deck p) := by
  ext φ e
  simp
  -- conjugation by `Homeomorph.refl E` inserts `refl` on both sides of `φ`, so the residual
  -- goal `↑((conjMulEquiv (Homeomorph.refl E) _) φ) e = ↑φ e` holds by definition.
  rfl

/-- Conjugating along a composite over-base homeomorphism is the composite of the two
conjugation equivalences. -/
@[simp]
lemma conjMulEquivTrans (h : E ≃ₜ F) (k : F ≃ₜ G)
    (hpq : ∀ e, q (h e) = p e) (hqr : ∀ f, r (k f) = q f) :
    conjMulEquiv (h.trans k) (fun e => by rw [Homeomorph.trans_apply, hqr, hpq]) =
      (conjMulEquiv h hpq).trans (conjMulEquiv k hqr) := by
  ext φ g
  simp

/-- Conjugation by the identity over-base homeomorphism maps a subgroup to itself. -/
lemma subgroup_map_conj_refl (H : Subgroup (Deck p)) :
    H.map ((conjMulEquiv (Homeomorph.refl E) (p := p) (q := p)
      (fun e => by rfl) : Deck p ≃* Deck p) : Deck p →* Deck p) = H := by
  rw [conjMulEquivRefl]
  simp

/-- Mapping a subgroup through two successive conjugations agrees with mapping it through the
conjugation attached to the composite over-base homeomorphism. -/
lemma subgroup_map_conj_trans (h : E ≃ₜ F) (k : F ≃ₜ G)
    (hpq : ∀ e, q (h e) = p e) (hqr : ∀ f, r (k f) = q f) (H : Subgroup (Deck p)) :
    (H.map ((conjMulEquiv h hpq : Deck p ≃* Deck q) : Deck p →* Deck q)).map
        ((conjMulEquiv k hqr : Deck q ≃* Deck r) : Deck q →* Deck r) =
      H.map ((conjMulEquiv (h.trans k)
        (fun e => by rw [Homeomorph.trans_apply, hqr, hpq]) : Deck p ≃* Deck r) :
          Deck p →* Deck r) := by
  rw [Subgroup.map_map]
  congr 1

end Deck

end TauCeti
