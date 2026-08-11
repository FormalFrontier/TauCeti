/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Conjugation
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Basic

/-!
# Transporting deck actions on fibres

An isomorphism of maps over a common base identifies corresponding fibres. This file packages
that fibre identification and records that it intertwines the restricted deck actions with
conjugation of deck transformations.

This is bookkeeping for the universal-covers roadmap: pointed cover isomorphisms carry chosen
lifts of the basepoint between fibres, and the pointed/unpointed cover correspondences need the
deck action on those fibres to be compatible with conjugating the deck group.

## Main definitions

* `TauCeti.Deck.fiberMap`: the homeomorphism between fibres induced by an over-base
  homeomorphism.
* `TauCeti.Deck.fiberMap_smul`: fibre transport intertwines the restricted deck actions via
  conjugation of deck transformations.
* `TauCeti.Deck.fiberMapStabilizerEquiv`: fibre transport identifies stabilizers via
  conjugation of deck transformations.
* `TauCeti.Deck.map_fiber_stabilizer_conjMulEquiv`: conjugation maps the source fibre
  stabilizer onto the transported target fibre stabilizer.
* `TauCeti.Deck.mem_orbit_fiberMap_iff`: fibre transport preserves deck-orbit membership.

## References

This supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stage 2
(`pointed` and `unpointed` connected cover correspondences), building on Stage 0.4's
deck-transformation group.
-/

public section

namespace TauCeti

namespace Deck

variable {E F G B : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
  {p : E → B} {q : F → B} {r : G → B} {b : B}

/-- An over-base homeomorphism identifies the fibre over `b` for `p` with the fibre over
`b` for `q`. -/
@[expose] def fiberMap (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (b : B) :
    p ⁻¹' {b} ≃ₜ q ⁻¹' {b} :=
  h.subtype fun e => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hpq]

/-- On underlying points, the fibre map induced by an over-base homeomorphism is just that
homeomorphism. -/
@[simp]
lemma fiberMap_apply_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b}) :
    (fiberMap h hpq b e : F) = h e.1 :=
  rfl

/-- On underlying points, the inverse fibre map is the inverse of the over-base
homeomorphism. -/
@[simp]
lemma fiberMap_symm_apply_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (f : q ⁻¹' {b}) :
    ((fiberMap h hpq b).symm f : E) = h.symm f.1 :=
  rfl

/-- The fibre map induced by the identity over-base homeomorphism is the identity. -/
@[simp]
lemma fiberMap_refl :
    fiberMap (Homeomorph.refl E) (p := p) (q := p) (fun _ => rfl) b =
      Homeomorph.refl (p ⁻¹' {b}) := by
  ext e
  rfl

/-- The inverse of the fibre map induced by an over-base homeomorphism is the fibre map induced
by the inverse over-base homeomorphism. -/
@[simp]
lemma fiberMap_symm (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) : (fiberMap h hpq b).symm =
      fiberMap h.symm (map_symm_eq_of_map_eq h hpq) b := by
  ext f
  rfl

/-- Fibre maps compose as the underlying over-base homeomorphisms compose. -/
@[simp]
lemma fiberMap_trans (h : E ≃ₜ F) (k : F ≃ₜ G)
    (hpq : ∀ e, q (h e) = p e) (hqr : ∀ f, r (k f) = q f) :
    (fiberMap h hpq b).trans (fiberMap k hqr b) =
      fiberMap (h.trans k) (fun e => by rw [Homeomorph.trans_apply, hqr, hpq]) b := by
  ext e
  rfl

/-- Fibre transport intertwines the restricted deck action with conjugation of deck
transformations. -/
@[simp]
lemma fiberMap_smul (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (φ : Deck p) (e : p ⁻¹' {b}) :
    fiberMap h hpq b (φ • e) = conjMulEquiv h hpq φ • fiberMap h hpq b e := by
  ext
  simp [fiber_smul_eq_fiberHomeomorph]

/-- The inverse fibre transport intertwines the restricted deck action with inverse
conjugation of deck transformations. -/
lemma fiberMap_symm_smul (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (ψ : Deck q) (f : q ⁻¹' {b}) :
    (fiberMap h hpq b).symm (ψ • f) = (conjMulEquiv h hpq).symm ψ • (fiberMap h hpq b).symm f := by
  ext
  simp [fiber_smul_eq_fiberHomeomorph]

/-- Transporting a deck transformation to the target cover and then restricting it to a fibre
is the same as restricting first and conjugating the resulting fibre homeomorphism by the fibre
transport map. -/
@[simp]
lemma fiberMap_trans_fiberHomeomorph (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (φ : Deck p) :
    (fiberMap h hpq b).trans (fiberHomeomorph (conjMulEquiv h hpq φ) b) =
      (fiberHomeomorph φ b).trans (fiberMap h hpq b) := by
  ext e
  simp

/-- Restricting conjugated deck transformations to a fibre is compatible with the fibre
restriction homomorphism. -/
@[simp]
lemma fiberHomeomorphHom_conjMulEquiv (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (φ : Deck p) :
    fiberHomeomorphHom q b (conjMulEquiv h hpq φ) =
      (fiberMap h hpq b).symm.trans ((fiberHomeomorphHom p b φ).trans (fiberMap h hpq b)) := by
  ext f
  simp

/-- Conjugation transports stabilizer membership along the fibre map. -/
@[grind =]
lemma mem_stabilizer_conjMulEquiv_fiberMap_iff (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (φ : Deck p) (e : p ⁻¹' {b}) :
    conjMulEquiv h hpq φ ∈ MulAction.stabilizer (Deck q) (fiberMap h hpq b e) ↔
      φ ∈ MulAction.stabilizer (Deck p) e := by
  constructor
  · intro hφ
    rw [MulAction.mem_stabilizer_iff] at hφ ⊢
    apply (fiberMap h hpq b).injective
    rw [fiberMap_smul]
    exact hφ
  · intro hφ
    rw [MulAction.mem_stabilizer_iff] at hφ ⊢
    rw [← fiberMap_smul, hφ]

/-- Conjugation maps the source fibre stabilizer onto the transported target fibre
stabilizer. -/
theorem map_fiber_stabilizer_conjMulEquiv (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b}) :
    (MulAction.stabilizer (Deck p) e).map ((conjMulEquiv h hpq : Deck p ≃* Deck q) :
        Deck p →* Deck q) =
      MulAction.stabilizer (Deck q) (fiberMap h hpq b e) := by
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact (mem_stabilizer_conjMulEquiv_fiberMap_iff h hpq φ e).mpr hφ
  · intro hψ
    refine ⟨(conjMulEquiv h hpq).symm ψ, ?_, by simp⟩
    exact (mem_stabilizer_conjMulEquiv_fiberMap_iff h hpq
      ((conjMulEquiv h hpq).symm ψ) e).mp (by simpa using hψ)

/-- Fibre transport identifies stabilizers, using conjugation on deck transformations. -/
def fiberMapStabilizerEquiv (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b}) :
    MulAction.stabilizer (Deck p) e ≃*
      MulAction.stabilizer (Deck q) (fiberMap h hpq b e) :=
  ((conjMulEquiv h hpq).subgroupMap (MulAction.stabilizer (Deck p) e)).trans
    (MulEquiv.subgroupCongr (map_fiber_stabilizer_conjMulEquiv h hpq e))

/-- On deck transformations, the fibre-map stabilizer equivalence is conjugation. -/
@[simp]
lemma fiberMapStabilizerEquiv_apply_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (e : p ⁻¹' {b}) (φ : MulAction.stabilizer (Deck p) e) :
    (fiberMapStabilizerEquiv h hpq e φ : Deck q) = conjMulEquiv h hpq φ.1 :=
  by simp [fiberMapStabilizerEquiv]

/-- On deck transformations, the inverse fibre-map stabilizer equivalence is inverse
conjugation. -/
@[simp]
lemma fiberMapStabilizerEquiv_symm_apply_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (e : p ⁻¹' {b}) (ψ : MulAction.stabilizer (Deck q) (fiberMap h hpq b e)) :
    ((fiberMapStabilizerEquiv h hpq e).symm ψ : Deck p) = (conjMulEquiv h hpq).symm ψ.1 :=
  by simp [fiberMapStabilizerEquiv]

/-- Applying a deck transformation and then transporting to the target fibre gives a point in
the target deck orbit. -/
lemma fiberMap_mem_orbit (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (φ : Deck p) (e : p ⁻¹' {b}) :
    fiberMap h hpq b (φ • e) ∈ MulAction.orbit (Deck q) (fiberMap h hpq b e) := by
  exact ⟨conjMulEquiv h hpq φ, fiberMap_smul h hpq φ e |>.symm⟩

/-- The fibre map carries the deck orbit of a point onto the deck orbit of the transported
point. -/
@[simp]
theorem fiberMap_image_orbit (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e : p ⁻¹' {b}) :
    fiberMap h hpq b '' MulAction.orbit (Deck p) e =
      MulAction.orbit (Deck q) (fiberMap h hpq b e) := by
  ext f
  constructor
  · rintro ⟨e', ⟨φ, hφ⟩, rfl⟩
    rw [← hφ]
    exact fiberMap_mem_orbit h hpq φ e
  · rintro ⟨ψ, rfl⟩
    refine ⟨(conjMulEquiv h hpq).symm ψ • e, ⟨(conjMulEquiv h hpq).symm ψ, rfl⟩, ?_⟩
    simp

/-- Applying a deck transformation and then transporting back to the source fibre gives a
point in the source deck orbit. -/
lemma fiberMap_symm_mem_orbit (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (ψ : Deck q) (f : q ⁻¹' {b}) :
    (fiberMap h hpq b).symm (ψ • f) ∈
      MulAction.orbit (Deck p) ((fiberMap h hpq b).symm f) := by
  exact ⟨(conjMulEquiv h hpq).symm ψ, fiberMap_symm_smul h hpq ψ f |>.symm⟩

/-- The inverse fibre map carries the deck orbit of a point onto the deck orbit of the
transported point. -/
theorem fiberMap_symm_image_orbit (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (f : q ⁻¹' {b}) :
    (fiberMap h hpq b).symm '' MulAction.orbit (Deck q) f =
      MulAction.orbit (Deck p) ((fiberMap h hpq b).symm f) := by
  ext e
  constructor
  · rintro ⟨f', ⟨ψ, hψ⟩, rfl⟩
    rw [← hψ]
    exact fiberMap_symm_mem_orbit h hpq ψ f
  · rintro ⟨φ, rfl⟩
    refine ⟨conjMulEquiv h hpq φ • f, ⟨conjMulEquiv h hpq φ, rfl⟩, ?_⟩
    simpa using fiberMap_symm_smul h hpq (conjMulEquiv h hpq φ) f

/-- Transporting both fibre points preserves membership in deck orbits. -/
@[simp]
theorem mem_orbit_fiberMap_iff (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e e' : p ⁻¹' {b}) :
    fiberMap h hpq b e' ∈ MulAction.orbit (Deck q) (fiberMap h hpq b e) ↔
      e' ∈ MulAction.orbit (Deck p) e := by
  constructor
  · rintro ⟨ψ, hψ⟩
    refine ⟨(conjMulEquiv h hpq).symm ψ, ?_⟩
    apply (fiberMap h hpq b).injective
    -- Injectivity changes the target to equality after applying the fibre map; the transport
    -- lemma rewrites that equality to the orbit witness supplied in the target fibre.
    change fiberMap h hpq b ((conjMulEquiv h hpq).symm ψ • e) = fiberMap h hpq b e'
    rw [fiberMap_smul]
    simpa using hψ
  · rintro ⟨φ, hφ⟩
    refine ⟨conjMulEquiv h hpq φ, ?_⟩
    -- The orbit witness is an equality of target-fibre points; exposing the fibre-map action
    -- shape lets `fiberMap_smul` turn it into the transported source witness.
    change conjMulEquiv h hpq φ • fiberMap h hpq b e = fiberMap h hpq b e'
    rw [← fiberMap_smul]
    exact congrArg (fiberMap h hpq b) hφ

/-- Transporting both target-fibre points back preserves membership in deck orbits. -/
theorem mem_orbit_fiberMap_symm_iff (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (f f' : q ⁻¹' {b}) :
    (fiberMap h hpq b).symm f' ∈
        MulAction.orbit (Deck p) ((fiberMap h hpq b).symm f) ↔
      f' ∈ MulAction.orbit (Deck q) f := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨conjMulEquiv h hpq φ, ?_⟩
    apply (fiberMap h hpq b).symm.injective
    -- As above, injectivity over the inverse fibre map leaves a definitional wrapper around the
    -- transported action, which `fiberMap_symm_smul` is stated to rewrite.
    change (fiberMap h hpq b).symm (conjMulEquiv h hpq φ • f) =
      (fiberMap h hpq b).symm f'
    rw [fiberMap_symm_smul]
    simpa using hφ
  · rintro ⟨ψ, hψ⟩
    refine ⟨(conjMulEquiv h hpq).symm ψ, ?_⟩
    -- The backward direction similarly exposes the source action so the inverse transport lemma
    -- can rewrite it to the congruence of the target orbit witness.
    change (conjMulEquiv h hpq).symm ψ • (fiberMap h hpq b).symm f =
      (fiberMap h hpq b).symm f'
    rw [← fiberMap_symm_smul]
    exact congrArg (fiberMap h hpq b).symm hψ

end Deck

end TauCeti
