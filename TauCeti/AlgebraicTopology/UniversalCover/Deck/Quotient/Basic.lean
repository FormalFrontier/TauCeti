/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular.Basic

/-!
# The orbit quotient of a regular deck action

For any map `p : E → B`, deck transformations preserve the value of `p`, so `p` factors
through the quotient of `E` by the orbit relation for the deck action. If the deck action is
regular, the induced map from the orbit quotient to the base is an equivalence.

This is algebraic bookkeeping for the universal-covers roadmap. Later quotient-cover and
regular-cover statements need to compare the base with the orbit space of the deck action,
but the basic equivalence only uses `Deck.IsRegular p`: surjectivity of `p` and transitivity
of the deck action on each fibre.

## Main declarations

* `TauCeti.Deck.orbitQuotientToBase`: the map `E / Deck p → B` induced by `p`.
* `TauCeti.Deck.IsRegular.orbitQuotientEquivBase`: for a regular deck action,
  `E / Deck p` is equivalent to the base.

## References

This supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stage 2, especially
the regular-cover milestones where fibres are deck orbits and quotient covers are compared
with the original base.
-/

public section

namespace TauCeti

namespace Deck

variable {E F B : Type*} [TopologicalSpace E] [TopologicalSpace F]
  {p : E → B} {q : F → B}

/-- Points in the same deck orbit have the same projection under `p`. -/
lemma eq_proj_of_orbitRel {e e' : E} (h : MulAction.orbitRel (Deck p) E e e') :
    p e = p e' := by
  rw [MulAction.orbitRel_apply] at h
  rcases h with ⟨φ, hφ⟩
  rw [← hφ]
  simpa [smul_eq_apply] using map_proj φ e'

/-- The projection map factors through the quotient of `E` by deck orbits. -/
@[expose] def orbitQuotientToBase (p : E → B) : MulAction.orbitRel.Quotient (Deck p) E → B :=
  Quotient.lift p fun _ _ h => eq_proj_of_orbitRel h

/-- The map from the deck-orbit quotient to the base evaluates on representatives by `p`. -/
@[simp]
lemma orbitQuotientToBase_mk (e : E) :
    orbitQuotientToBase p (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) =
      p e :=
  rfl

/-- If deck orbits are exactly fibres of `p`, the deck-orbit relation is the kernel relation
of `p`. -/
private lemma orbitRel_eq_ker_of_exists_apply_eq
    (hpoint : ∀ {e e' : E}, p e = p e' → ∃ φ : Deck p, φ.1 e = e') :
    MulAction.orbitRel (Deck p) E = Setoid.ker p := by
  ext e e'
  constructor
  · exact eq_proj_of_orbitRel
  · intro heq
    rcases hpoint heq with ⟨φ, hφ⟩
    exact ⟨φ⁻¹, by
      have hinv : φ.1.symm e' = e := by
        rw [← hφ, Homeomorph.symm_apply_apply]
      simpa [smul_eq_apply] using hinv⟩

/-- If every pair of points with the same projection is connected by a deck transformation,
then two points of the total space have the same projection exactly when they lie in a common
orbit of the deck transformation group. The reverse direction holds because deck
transformations preserve the projection. -/
lemma apply_eq_iff_mem_orbit_of_exists_apply_eq
    (hpoint : ∀ {e e' : E}, p e = p e' → ∃ φ : Deck p, φ.1 e = e') {e₁ e₂ : E} :
    p e₁ = p e₂ ↔ e₁ ∈ MulAction.orbit (Deck p) e₂ := by
  rw [← MulAction.orbitRel_apply, orbitRel_eq_ker_of_exists_apply_eq hpoint, Setoid.ker_def]

/-- An over-base homeomorphism preserves the corresponding deck-orbit relations. -/
lemma orbitRel_homeomorph_iff (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e e' : E) :
    MulAction.orbitRel (Deck p) E e e' ↔
      MulAction.orbitRel (Deck q) F (h e) (h e') := by
  constructor
  · intro hee'
    rw [MulAction.orbitRel_apply] at hee' ⊢
    rcases hee' with ⟨φ, hφ⟩
    refine ⟨conjMulEquiv h hpq φ, ?_⟩
    have hφ_apply : φ.1 e' = e := by
      simpa only [smul_eq_apply] using hφ
    calc
      (conjMulEquiv h hpq φ) • h e' = (conjMulEquiv h hpq φ).1 (h e') :=
        smul_eq_apply _ _
      _ = h (φ.1 e') := by rw [conjMulEquiv_apply_coe, h.symm_apply_apply]
      _ = h e := by rw [hφ_apply]
  · intro hff'
    rw [MulAction.orbitRel_apply] at hff' ⊢
    rcases hff' with ⟨ψ, hψ⟩
    refine ⟨(conjMulEquiv h hpq).symm ψ, ?_⟩
    have hψ_apply : ψ.1 (h e') = h e := by
      simpa only [smul_eq_apply] using hψ
    calc
      ((conjMulEquiv h hpq).symm ψ) • e' =
          ((conjMulEquiv h hpq).symm ψ).1 e' := smul_eq_apply _ _
      _ = h.symm (ψ.1 (h e')) := conjMulEquiv_symm_apply_coe h hpq ψ e'
      _ = e := by rw [hψ_apply, h.symm_apply_apply]

/-- An over-base homeomorphism identifies the corresponding deck-orbit quotients. -/
@[expose] def orbitQuotientEquiv (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) :
    MulAction.orbitRel.Quotient (Deck p) E ≃ MulAction.orbitRel.Quotient (Deck q) F :=
  Quotient.congr h.toEquiv (orbitRel_homeomorph_iff h hpq)

/-- The over-base equivalence on orbit quotients evaluates on representatives by the
homeomorphism. -/
@[simp]
lemma orbitQuotientEquiv_mk (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (e : E) :
    orbitQuotientEquiv h hpq
      (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) =
        (Quotient.mk'' (h e) : MulAction.orbitRel.Quotient (Deck q) F) :=
  rfl

/-- The inverse over-base equivalence on orbit quotients evaluates on representatives by the
inverse homeomorphism. -/
@[simp]
lemma orbitQuotientEquiv_symm_mk (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (f : F) :
    (orbitQuotientEquiv h hpq).symm (Quotient.mk'' f : MulAction.orbitRel.Quotient (Deck q) F) =
        (Quotient.mk'' (h.symm f) : MulAction.orbitRel.Quotient (Deck p) E) :=
  rfl

/-- If deck transformations act transitively on each fibre of `p`, the map from the
deck-orbit quotient to the base is injective. -/
lemma orbitQuotientToBase_injective_of_exists_apply_eq
    (hpoint : ∀ {e e' : E}, p e = p e' → ∃ φ : Deck p, φ.1 e = e') :
    Function.Injective (orbitQuotientToBase p) := by
  exact (Setoid.lift_injective_iff_ker_eq_of_le
    (r := MulAction.orbitRel (Deck p) E) (f := p)
    (fun _ _ h => eq_proj_of_orbitRel h)).mpr
      (orbitRel_eq_ker_of_exists_apply_eq hpoint).symm

/-- If deck transformations act transitively on each fibre of `p`, two points have the same
deck-orbit quotient class exactly when they have the same projection. -/
lemma orbitQuotient_mk_eq_mk_iff_of_exists_apply_eq
    (hpoint : ∀ {e e' : E}, p e = p e' → ∃ φ : Deck p, φ.1 e = e') (e e' : E) :
    (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) = Quotient.mk'' e' ↔
      p e = p e' := by
  constructor
  · intro h
    simpa only [orbitQuotientToBase_mk] using congr_arg (orbitQuotientToBase p) h
  · intro h
    apply orbitQuotientToBase_injective_of_exists_apply_eq hpoint
    simpa only [orbitQuotientToBase_mk] using h

namespace IsRegular

/-- For a regular deck action, the map from deck-orbit quotient to the base is injective. -/
lemma orbitQuotientToBase_injective (hreg : IsRegular p) :
    Function.Injective (orbitQuotientToBase p) := by
  exact orbitQuotientToBase_injective_of_exists_apply_eq (isRegular_iff_exists_apply_eq.mp hreg).2

/-- For a regular deck action, two points have the same projection exactly when they lie in a
common deck orbit. -/
lemma apply_eq_iff_mem_orbit (hreg : IsRegular p) {e₁ e₂ : E} :
    p e₁ = p e₂ ↔ e₁ ∈ MulAction.orbit (Deck p) e₂ :=
  Deck.apply_eq_iff_mem_orbit_of_exists_apply_eq (isRegular_iff_exists_apply_eq.mp hreg).2

/-- A regular deck action identifies the quotient of the total space by deck orbits with the
base. -/
@[expose] noncomputable def orbitQuotientEquivBase (hreg : IsRegular p) :
    MulAction.orbitRel.Quotient (Deck p) E ≃ B :=
  Equiv.ofBijective (orbitQuotientToBase p)
    ⟨hreg.orbitQuotientToBase_injective, Quotient.lift_surjective p _ hreg.1⟩

/-- The equivalence from the deck-orbit quotient to the base evaluates on representatives by
the projection map. -/
@[simp]
lemma orbitQuotientEquivBase_mk (hreg : IsRegular p) (e : E) :
    hreg.orbitQuotientEquivBase
      (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) = p e :=
  rfl

/-- The inverse quotient-base equivalence sends a projected point to the class of any lift. -/
@[simp]
lemma orbitQuotientEquivBase_symm_apply_proj (hreg : IsRegular p) (e : E) :
    hreg.orbitQuotientEquivBase.symm (p e) =
      (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) := by
  apply hreg.orbitQuotientEquivBase.injective
  rw [Equiv.apply_symm_apply, orbitQuotientEquivBase_mk]

/-- For a regular deck action, two points have the same deck-orbit quotient class exactly when
they have the same projection. -/
@[simp]
lemma orbitQuotient_mk_eq_mk_iff (hreg : IsRegular p) (e e' : E) :
    (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) = Quotient.mk'' e' ↔
      p e = p e' := by
  exact orbitQuotient_mk_eq_mk_iff_of_exists_apply_eq
    (isRegular_iff_exists_apply_eq.mp hreg).2 e e'

/-- Transporting a regular deck action along an over-base homeomorphism is compatible with
the corresponding orbit-quotient equivalences. -/
lemma orbitQuotientEquivBase_conj (hreg : IsRegular p) (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (x : MulAction.orbitRel.Quotient (Deck p) E) :
    (hreg.conj h hpq).orbitQuotientEquivBase
      (orbitQuotientEquiv h hpq x) = hreg.orbitQuotientEquivBase x := by
  induction x using Quotient.inductionOn' with
  | h e =>
      rw [orbitQuotientEquiv_mk, orbitQuotientEquivBase_mk, orbitQuotientEquivBase_mk]
      exact hpq e

/-- Representative form of compatibility between over-base homeomorphisms and the regular
orbit-quotient equivalences. -/
lemma orbitQuotientEquivBase_conj_mk (hreg : IsRegular p) (h : E ≃ₜ F)
    (hpq : ∀ e, q (h e) = p e) (f : F) : (hreg.conj h hpq).orbitQuotientEquivBase
      (Quotient.mk'' f : MulAction.orbitRel.Quotient (Deck q) F) =
        hreg.orbitQuotientEquivBase
          (Quotient.mk'' (h.symm f) : MulAction.orbitRel.Quotient (Deck p) E) := by
  rw [← orbitQuotientEquiv_symm_mk h hpq f,
    ← hreg.orbitQuotientEquivBase_conj h hpq ((orbitQuotientEquiv h hpq).symm
      (Quotient.mk'' f : MulAction.orbitRel.Quotient (Deck q) F)),
    (orbitQuotientEquiv h hpq).apply_symm_apply]

end IsRegular

end Deck

end TauCeti
