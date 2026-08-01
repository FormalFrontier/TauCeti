/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Topology.Covering.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Basic

/-!
# Deck transformations of connected covers

For a covering projection with preconnected total space, two deck transformations are equal as
soon as they agree at one point. Equivalently, the deck action on the total space is
cancellative, and so is the induced action on every fibre.

This is a small prerequisite for the universal-covers roadmap Stage 2: the pointed and
unpointed cover correspondences need to track deck transformations through their action on a
chosen fibre, and regular-cover statements use the fact that a deck transformation of a
connected cover cannot fix a point unless it is the identity.

## Main declarations

* `TauCeti.Deck.orbitMap_injective`: evaluation at a fibre point is injective on deck
  transformations of a preconnected covering.
* `TauCeti.Deck.deckEquivFiberOfSurjective`: if that evaluation map is also surjective, it
  identifies the deck group with the chosen fibre.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- Two deck transformations of a covering map with preconnected total space are equal if they
agree at one point of the total space. -/
theorem eq_of_apply_eq [PreconnectedSpace E] (hp : IsCoveringMap p) (φ ψ : Deck p) {e : E}
    (h : φ.1 e = ψ.1 e) : φ = ψ := by
  apply Subtype.ext
  apply Homeomorph.ext
  exact congr_fun
    (hp.eq_of_comp_eq φ.1.continuous ψ.1.continuous
      (by
        ext x
        rw [Function.comp_apply, Function.comp_apply, map_proj φ x, map_proj ψ x])
      e h)

/-- On a covering map with preconnected total space, equality of the ambient deck action at one
point determines the deck transformation. -/
theorem eq_of_smul_eq_smul [PreconnectedSpace E] (hp : IsCoveringMap p) (φ ψ : Deck p) {e : E}
    (h : φ • e = ψ • e) : φ = ψ :=
  eq_of_apply_eq hp φ ψ (by simpa only [smul_eq_apply] using h)

/-- The deck action on the total space of a preconnected covering is cancellative. -/
theorem isCancelSMul [PreconnectedSpace E] (hp : IsCoveringMap p) : IsCancelSMul (Deck p) E where
  right_cancel' φ ψ _ h := eq_of_smul_eq_smul hp φ ψ h

/-- The stabilizer of any point under the deck action of a preconnected covering is trivial. -/
@[simp]
theorem stabilizer_eq_bot [PreconnectedSpace E] (hp : IsCoveringMap p) (e : E) :
    MulAction.stabilizer (Deck p) e = ⊥ := by
  haveI := isCancelSMul hp
  exact IsCancelSMul.stabilizer_eq_bot e

section Fiber

variable {b : B}

/-- A deck transformation of a preconnected covering is determined by its action on one point of
a chosen fibre. -/
theorem eq_of_fiber_smul_eq_fiber_smul [PreconnectedSpace E] (hp : IsCoveringMap p)
    (φ ψ : Deck p) {e : p ⁻¹' {b}} (h : φ • e = ψ • e) : φ = ψ := by
  have hcoe : (φ • e : E) = (ψ • e : E) := congrArg Subtype.val h
  rw [smul_eq_apply, smul_eq_apply] at hcoe
  exact eq_of_apply_eq hp φ ψ hcoe

/-- A deck transformation of a preconnected covering is determined by the value of its
restricted fibre homeomorphism at one point. -/
theorem eq_of_fiberHomeomorph_apply_eq [PreconnectedSpace E] (hp : IsCoveringMap p)
    (φ ψ : Deck p) {e : p ⁻¹' {b}} (h : fiberHomeomorph φ b e = fiberHomeomorph ψ b e) :
    φ = ψ :=
  eq_of_fiber_smul_eq_fiber_smul hp φ ψ (by simpa [fiber_smul_eq_fiberHomeomorph] using h)

/-- The induced deck action on a fibre of a preconnected covering is cancellative. -/
theorem fiber_isCancelSMul [PreconnectedSpace E] (hp : IsCoveringMap p) :
    IsCancelSMul (Deck p) (p ⁻¹' {b}) where
  right_cancel' φ ψ _ h := eq_of_fiber_smul_eq_fiber_smul hp φ ψ h

/-- The stabilizer of any fibre point under the restricted deck action of a preconnected
covering is trivial. -/
@[simp]
theorem fiber_stabilizer_eq_bot [PreconnectedSpace E] (hp : IsCoveringMap p) (e : p ⁻¹' {b}) :
    MulAction.stabilizer (Deck p) e = ⊥ := by
  haveI := fiber_isCancelSMul (b := b) hp
  exact IsCancelSMul.stabilizer_eq_bot e

/-- For a nonempty fibre of a preconnected covering, restricting deck transformations to that
fibre is injective. -/
theorem fiberHomeomorphHom_injective [PreconnectedSpace E] (hp : IsCoveringMap p)
    [Nonempty (p ⁻¹' {b})] : Function.Injective (fiberHomeomorphHom p b) := by
  classical
  intro φ ψ hφψ
  exact eq_of_fiberHomeomorph_apply_eq hp φ ψ (congr_fun (congr_arg DFunLike.coe hφψ)
    (Classical.arbitrary (p ⁻¹' {b})))

/-- For a nonempty fibre of a preconnected covering, the homomorphism restricting deck
transformations to that fibre has trivial kernel. -/
@[simp]
theorem fiberHomeomorphHom_ker_eq_bot [PreconnectedSpace E] (hp : IsCoveringMap p)
    [Nonempty (p ⁻¹' {b})] : MonoidHom.ker (fiberHomeomorphHom p b) = ⊥ :=
  (MonoidHom.ker_eq_bot_iff (fiberHomeomorphHom p b)).mpr (fiberHomeomorphHom_injective hp)

/-- Evaluation at a point in a fibre is injective for a preconnected covering. -/
lemma orbitMap_injective [PreconnectedSpace E] (hp : IsCoveringMap p) (e : p ⁻¹' {b}) :
    Function.Injective fun φ : Deck p => φ • e := by
  intro φ ψ hφψ
  exact eq_of_fiber_smul_eq_fiber_smul hp φ ψ hφψ

/-- For a preconnected covering whose orbit map at the chosen fibre point is surjective,
evaluation at that point identifies the deck group with that fibre.

This is the simply-transitive fibre action package used later when regular covers are
compared with normal subgroups and normalizer quotients. -/
@[expose] noncomputable def deckEquivFiberOfSurjective [PreconnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {b}) (hsurj : Function.Surjective fun φ : Deck p => φ • e) :
    Deck p ≃ p ⁻¹' {b} :=
  Equiv.ofBijective (fun φ : Deck p => φ • e)
    ⟨orbitMap_injective hp e, hsurj⟩

/-- The local equivalence from deck transformations to a fibre evaluates a deck
transformation at the chosen fibre point. -/
@[simp]
lemma deckEquivFiberOfSurjective_apply [PreconnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {b}) (hsurj : Function.Surjective fun φ : Deck p => φ • e) (φ : Deck p) :
    deckEquivFiberOfSurjective hp e hsurj φ = φ • e :=
  rfl

/-- On underlying points, the local deck-to-fibre equivalence is evaluation of the
underlying homeomorphism. -/
lemma deckEquivFiberOfSurjective_apply_coe [PreconnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {b}) (hsurj : Function.Surjective fun φ : Deck p => φ • e) (φ : Deck p) :
    (deckEquivFiberOfSurjective hp e hsurj φ : E) = φ.1 e.1 := by
  rw [deckEquivFiberOfSurjective_apply]
  exact fiber_smul_coe φ e

/-- The inverse of `deckEquivFiberOfSurjective` is characterized by the deck transformation it
returns: it sends the chosen fibre point to the requested fibre point. -/
@[simp]
lemma deckEquivFiberOfSurjective_symm_smul [PreconnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {b}) (hsurj : Function.Surjective fun φ : Deck p => φ • e) (e' : p ⁻¹' {b}) :
    (deckEquivFiberOfSurjective hp e hsurj).symm e' • e = e' :=
  (deckEquivFiberOfSurjective hp e hsurj).apply_symm_apply e'

/-- On underlying points, the inverse of `deckEquivFiberOfSurjective` sends the chosen point to
the requested point. -/
@[simp]
lemma deckEquivFiberOfSurjective_symm_apply_coe [PreconnectedSpace E]
    (hp : IsCoveringMap p) (e : p ⁻¹' {b})
    (hsurj : Function.Surjective fun φ : Deck p => φ • e) (e' : p ⁻¹' {b}) :
    (((deckEquivFiberOfSurjective hp e hsurj).symm e').1 e.1 : E) = e'.1 := by
  simpa only [fiber_smul_eq_fiberHomeomorph, fiberHomeomorph_apply] using
    congrArg Subtype.val (deckEquivFiberOfSurjective_symm_smul hp e hsurj e')

/-- The local deck-to-fibre equivalence sends the identity to the chosen base point. -/
lemma deckEquivFiberOfSurjective_one [PreconnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {b}) (hsurj : Function.Surjective fun φ : Deck p => φ • e) :
    deckEquivFiberOfSurjective hp e hsurj 1 = e := by
  rw [deckEquivFiberOfSurjective_apply, one_smul]

/-- The local deck-to-fibre equivalence is equivariant for left multiplication on the deck
group and the deck action on the fibre. -/
lemma deckEquivFiberOfSurjective_mul [PreconnectedSpace E] (hp : IsCoveringMap p)
    (e : p ⁻¹' {b}) (hsurj : Function.Surjective fun φ : Deck p => φ • e) (φ ψ : Deck p) :
    deckEquivFiberOfSurjective hp e hsurj (φ * ψ) =
      φ • deckEquivFiberOfSurjective hp e hsurj ψ := by
  rw [deckEquivFiberOfSurjective_apply, deckEquivFiberOfSurjective_apply, mul_smul]

/-- Translating a fibre point before applying the inverse local equivalence multiplies the
corresponding deck transformation on the left. -/
@[simp]
lemma deckEquivFiberOfSurjective_symm_apply_smul [PreconnectedSpace E]
    (hp : IsCoveringMap p) (e : p ⁻¹' {b})
    (hsurj : Function.Surjective fun φ : Deck p => φ • e) (e' : p ⁻¹' {b}) (φ : Deck p) :
    (deckEquivFiberOfSurjective hp e hsurj).symm (φ • e') =
      φ * (deckEquivFiberOfSurjective hp e hsurj).symm e' := by
  apply (deckEquivFiberOfSurjective hp e hsurj).injective
  rw [Equiv.apply_symm_apply, deckEquivFiberOfSurjective_mul, Equiv.apply_symm_apply]

end Fiber

end Deck

end TauCeti
