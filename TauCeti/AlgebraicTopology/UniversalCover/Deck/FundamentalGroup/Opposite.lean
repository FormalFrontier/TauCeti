/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.FundamentalGroup.Basic
public import TauCeti.Topology.Homotopy.Covering

/-!
# Deck transformations as the opposite fundamental group

For a regular covering map `p : E → X` with simply connected total space, the existing
comparison

  `Deck.IsRegular.fundamentalGroupEquiv : FundamentalGroup X x ≃* (Deck p)ᵐᵒᵖ`

pins the convention required by the universal-covers roadmap: monodromy acts on the right,
whereas deck transformations act on the left. This file packages the equivalent
deck-to-fundamental-group form

  `Deck p ≃* (FundamentalGroup X x)ᵐᵒᵖ`

and records its pointwise characterizations. This is a small API layer for the Stage 1
comparison `Deck(proj) ≃* π₁(X, x₀)` (up to the opposite dictated by the convention), and
for later cover-classification arguments that pass between deck transformations, loop
classes, and fibre points.

## Main declarations

* `TauCeti.Deck.IsRegular.deckFundamentalGroupEquiv`: the deck group is isomorphic to the
  opposite fundamental group.
* `TauCeti.Deck.IsRegular.deckFundamentalGroupEquiv_unop_monodromy`: the loop class
  attached to a deck transformation has monodromy equal to that deck transformation on the
  chosen lift.
* `TauCeti.Deck.IsRegular.deckEquivFiber_eq_fundamentalGroupEquivFiber`: the deck-to-fibre
  equivalence and monodromy-to-fibre equivalence agree under this comparison.

## References

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 1
(`Deck(proj) ≃* π₁(X, x₀)`, possibly up to `ᵐᵒᵖ`). It is a formal consequence of
`TauCeti.Deck.IsRegular.fundamentalGroupEquiv`, which in turn uses Junyan Xu's
`IsQuotientCoveringMap.fundamentalGroupEquiv` from `Mathlib.Topology.Homotopy.Lifting`.
-/

public section

namespace TauCeti

namespace Deck

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {x : X}

namespace IsRegular

/-- For a regular covering map `p : E → X` with simply connected total space, the deck group
is isomorphic to the opposite of the fundamental group of the base:
`Deck p ≃* (FundamentalGroup X x)ᵐᵒᵖ`.

The opposite is the same convention as in `fundamentalGroupEquiv`: deck transformations act
on the left, while fundamental-group monodromy acts on the right. -/
-- The public `rfl` characterization lemmas below need this exposed under Lean's module
-- export rules, as in the nearby deck-to-fibre equivalences.
@[expose] noncomputable def deckFundamentalGroupEquiv [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) :
    Deck p ≃* (FundamentalGroup X x)ᵐᵒᵖ :=
  (MulEquiv.opOp (Deck p)).trans (MulEquiv.op (hreg.fundamentalGroupEquiv hp e).symm)

/-- The deck-to-fundamental-group equivalence sends a deck transformation to the opposite
of the loop class corresponding to the opposite deck transformation under
`fundamentalGroupEquiv`. -/
@[simp]
lemma deckFundamentalGroupEquiv_apply [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (φ : Deck p) :
    hreg.deckFundamentalGroupEquiv hp e φ =
      MulOpposite.op ((hreg.fundamentalGroupEquiv hp e).symm (MulOpposite.op φ)) :=
  rfl

/-- The inverse deck-to-fundamental-group equivalence sends `op γ` to the deck
transformation corresponding to `γ` under `fundamentalGroupEquiv`. -/
@[simp]
lemma deckFundamentalGroupEquiv_symm_op [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    (hreg.deckFundamentalGroupEquiv hp e).symm (MulOpposite.op γ) =
      (hreg.fundamentalGroupEquiv hp e γ).unop :=
  rfl

/-- The loop class attached to a deck transformation has monodromy equal to that deck
transformation on the chosen lift. -/
lemma deckFundamentalGroupEquiv_unop_monodromy [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (φ : Deck p) :
    (hp.monodromy ((hreg.deckFundamentalGroupEquiv hp e φ).unop) e : E) = φ • (e : E) := by
  rw [deckFundamentalGroupEquiv_apply, MulOpposite.unop_op]
  exact fundamentalGroupEquiv_symm_op_monodromy hreg hp e φ

/-- A deck transformation corresponds to a loop class exactly when that loop class's
monodromy moves the chosen lift by the deck transformation. -/
lemma deckFundamentalGroupEquiv_apply_eq_op_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (φ : Deck p) (γ : FundamentalGroup X x) :
    hreg.deckFundamentalGroupEquiv hp e φ = MulOpposite.op γ ↔
      (hp.monodromy γ e : E) = φ • (e : E) := by
  constructor
  · intro h
    have hunop : (hreg.deckFundamentalGroupEquiv hp e φ).unop = γ := by
      rw [h, MulOpposite.unop_op]
    rw [← hunop]
    exact deckFundamentalGroupEquiv_unop_monodromy hreg hp e φ
  · intro hmono
    have hF : hreg.fundamentalGroupEquiv hp e γ = MulOpposite.op φ :=
      (fundamentalGroupEquiv_apply_eq_iff hreg hp e γ (MulOpposite.op φ)).2
        (by simpa [eq_comm] using hmono)
    have hsymm : (hreg.deckFundamentalGroupEquiv hp e).symm (MulOpposite.op γ) = φ := by
      rw [deckFundamentalGroupEquiv_symm_op, hF, MulOpposite.unop_op]
    rw [← hsymm]
    exact (hreg.deckFundamentalGroupEquiv hp e).apply_symm_apply (MulOpposite.op γ)

/-- The inverse comparison is characterized by the same monodromy formula. -/
lemma deckFundamentalGroupEquiv_symm_op_eq_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (γ : FundamentalGroup X x) (φ : Deck p) :
    (hreg.deckFundamentalGroupEquiv hp e).symm (MulOpposite.op γ) = φ ↔
      (hp.monodromy γ e : E) = φ • (e : E) := by
  rw [← deckFundamentalGroupEquiv_apply_eq_op_iff hreg hp e φ γ]
  constructor
  · intro h
    rw [← h]
    exact (hreg.deckFundamentalGroupEquiv hp e).apply_symm_apply (MulOpposite.op γ)
  · intro h
    rw [← h]
    exact (hreg.deckFundamentalGroupEquiv hp e).symm_apply_apply φ

/-- A deck transformation maps to the identity loop class exactly when it fixes the chosen
lift. -/
lemma deckFundamentalGroupEquiv_eq_one_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (φ : Deck p) :
    hreg.deckFundamentalGroupEquiv hp e φ = 1 ↔ φ • (e : E) = e := by
  rw [← MulOpposite.op_one, deckFundamentalGroupEquiv_apply_eq_op_iff]
  have hmon : (hp.monodromy (1 : FundamentalGroup X x) e : E) = e := by
    exact congrArg Subtype.val ((fundamentalGroupEquiv_eq_one_iff hreg hp e 1).1 (by simp))
  rw [hmon]
  constructor
  · intro h
    exact h.symm
  · intro h
    exact h.symm

/-- Under the deck-to-fundamental-group comparison, the deck-to-fibre equivalence for a
regular cover agrees with the monodromy equivalence from `π₁` to the same fibre. -/
lemma deckEquivFiber_eq_fundamentalGroupEquivFiber [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (φ : Deck p) :
    deckEquivFiber hp hreg e φ =
      TauCeti.IsCoveringMap.fundamentalGroupEquivFiber hp e
        ((hreg.deckFundamentalGroupEquiv hp e φ).unop) := by
  ext
  rw [deckEquivFiber_apply_coe, TauCeti.IsCoveringMap.fundamentalGroupEquivFiber_apply_coe,
    deckFundamentalGroupEquiv_unop_monodromy]
  exact (smul_eq_apply φ (e : E)).symm

end IsRegular

end Deck

end TauCeti
