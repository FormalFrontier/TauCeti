/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Basic
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# The action of deck transformations on a fibre

A deck transformation preserves every fibre of the projection. This file packages that
restriction as a multiplicative homomorphism from the deck transformation group to the
homeomorphism group of a chosen fibre, and records the induced action on that fibre.

This is bookkeeping for the universal-covers roadmap: the later comparison between deck
transformations and the fundamental group, and the regular-cover statements, use the action of
deck transformations on individual fibres rather than only on the total space.

## Main definitions

* `TauCeti.Deck.fiberHomeomorphHom`: the homomorphism
  `Deck p →* (p ⁻¹' {b} ≃ₜ p ⁻¹' {b})`.
* `TauCeti.Deck.instFiberMulAction`: the induced action of `Deck p` on the fibre over `b`.
* `TauCeti.Deck.mem_fiber_stabilizer_iff_coe`: membership in a fibre stabilizer is equality
  on the underlying point.

## References

This supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stage 0.4
(`Deck p` as the deck transformation group), and the later deck-group action on fibres in
Stages 1 and 2.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- The homomorphism from deck transformations to homeomorphisms of the fibre over `b`.

It sends a deck transformation to its restriction to the subtype `p ⁻¹' {b}`. -/
@[expose] def fiberHomeomorphHom (p : E → B) (b : B) : Deck p →* (p ⁻¹' {b} ≃ₜ p ⁻¹' {b}) where
  toFun φ := fiberHomeomorph φ b
  map_one' := by
    ext e
    rfl
  map_mul' φ ψ := by
    ext e
    rfl

/-- The fibre homomorphism evaluates by applying the deck transformation to the underlying
point of the fibre. -/
@[simp]
lemma fiberHomeomorphHom_apply (φ : Deck p) (e : p ⁻¹' {b}) :
    fiberHomeomorphHom p b φ e = fiberHomeomorph φ b e :=
  rfl

/-- On underlying points, the fibre homomorphism is evaluation of the underlying
homeomorphism. -/
@[simp]
lemma fiberHomeomorphHom_apply_coe (φ : Deck p) (e : p ⁻¹' {b}) :
    (fiberHomeomorphHom p b φ e : E) = φ.1 e.1 :=
  rfl

/-- The fibre homomorphism sends the identity deck transformation to the identity
homeomorphism of the fibre. -/
@[simp]
lemma fiberHomeomorphHom_one :
    fiberHomeomorphHom p b (1 : Deck p) = 1 := by
  exact (fiberHomeomorphHom p b).map_one

/-- The fibre homomorphism sends products of deck transformations to products of fibre
homeomorphisms. -/
@[simp]
lemma fiberHomeomorphHom_mul (φ ψ : Deck p) :
    fiberHomeomorphHom p b (φ * ψ) = fiberHomeomorphHom p b φ * fiberHomeomorphHom p b ψ := by
  exact (fiberHomeomorphHom p b).map_mul φ ψ

/-- The fibre homomorphism sends inverses of deck transformations to inverses of fibre
homeomorphisms. -/
@[simp]
lemma fiberHomeomorphHom_inv (φ : Deck p) :
    fiberHomeomorphHom p b φ⁻¹ = (fiberHomeomorphHom p b φ)⁻¹ := by
  exact (fiberHomeomorphHom p b).map_inv φ

/-- The fibre homeomorphism associated to the identity deck transformation is the identity. -/
@[simp]
lemma fiberHomeomorph_one :
    fiberHomeomorph (1 : Deck p) b = 1 := by
  exact fiberHomeomorphHom_one

/-- The fibre homeomorphism associated to a product is the product of the associated fibre
homeomorphisms. -/
@[simp]
lemma fiberHomeomorph_mul (φ ψ : Deck p) :
    fiberHomeomorph (φ * ψ) b = fiberHomeomorph φ b * fiberHomeomorph ψ b := by
  exact fiberHomeomorphHom_mul φ ψ

/-- The fibre homeomorphism associated to an inverse is the inverse of the associated fibre
homeomorphism. -/
@[simp]
lemma fiberHomeomorph_inv (φ : Deck p) :
    fiberHomeomorph φ⁻¹ b = (fiberHomeomorph φ b)⁻¹ := by
  exact fiberHomeomorphHom_inv φ

/-- The fibre homeomorphism associated to a natural-number power is the corresponding power
of the associated fibre homeomorphism. -/
@[simp]
lemma fiberHomeomorph_pow (φ : Deck p) (n : ℕ) :
    fiberHomeomorph (φ ^ n) b = fiberHomeomorph φ b ^ n := by
  exact (fiberHomeomorphHom p b).map_pow φ n

/-- The fibre homeomorphism associated to an integer power is the corresponding power of the
associated fibre homeomorphism. -/
@[simp]
lemma fiberHomeomorph_zpow (φ : Deck p) (n : ℤ) :
    fiberHomeomorph (φ ^ n) b = fiberHomeomorph φ b ^ n := by
  exact (fiberHomeomorphHom p b).map_zpow φ n

/-- Deck transformations act on each fibre by restricting their action on the total space. -/
instance instFiberMulAction : MulAction (Deck p) (p ⁻¹' {b}) :=
  MulAction.compHom (p ⁻¹' {b}) (fiberHomeomorphHom p b)

/-- The fibre action is evaluation of the fibre homeomorphism. -/
lemma fiber_smul_eq_fiberHomeomorph (φ : Deck p) (e : p ⁻¹' {b}) :
    φ • e = fiberHomeomorph φ b e :=
  rfl

/-- On underlying points, the fibre action is evaluation of the underlying deck
transformation. -/
@[simp]
lemma fiber_smul_coe (φ : Deck p) (e : p ⁻¹' {b}) : ((φ • e : p ⁻¹' {b}) : E) = φ.1 e.1 :=
  rfl

/-- The projection value of a point in the fibre is unchanged after the restricted deck
action. -/
lemma map_fiber_smul (φ : Deck p) (e : p ⁻¹' {b}) :
    p (φ • e : E) = b := by
  exact (φ • e).2

/-- The restricted deck action keeps points in the fibre over `b`. -/
lemma fiber_smul_mem (φ : Deck p) (e : p ⁻¹' {b}) : (φ • e : E) ∈ p ⁻¹' {b} := by
  exact map_fiber_smul φ e

/-- The restricted fibre action agrees with the ambient action on the total space after
coercing out of the fibre subtype. -/
lemma fiber_smul_coe_eq_smul (φ : Deck p) (e : p ⁻¹' {b}) :
    ((φ • e : p ⁻¹' {b}) : E) = φ • (e : E) := by
  trans φ.1 e.1
  · exact fiber_smul_coe φ e
  · exact (smul_eq_apply φ (e : E)).symm

/-- Membership in the stabilizer of a fibre point is equality on the underlying point. -/
@[grind =]
lemma mem_fiber_stabilizer_iff_coe (φ : Deck p) (e : p ⁻¹' {b}) :
    φ ∈ MulAction.stabilizer (Deck p) e ↔ φ.1 e.1 = e.1 := by
  simp [Subtype.ext_iff, fiber_smul_eq_fiberHomeomorph]

end Deck

end TauCeti
