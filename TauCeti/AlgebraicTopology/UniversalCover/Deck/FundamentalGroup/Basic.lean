/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.MulOpposite
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.Covering
public import Mathlib.Topology.Homotopy.Lifting

/-!
# The fundamental group of the base of a regular cover and its deck group

For a covering map `p : E → X` with **simply connected** total space whose deck action is
**regular** (`p` surjective, with `Deck p` acting transitively on every fibre), the
fundamental group of the base is anti-isomorphic to the deck transformation group:

  `FundamentalGroup X x ≃* (Deck p)ᵐᵒᵖ`.

This is the regular-cover comparison needed for the Stage 1 universal-covers roadmap target
(`Deck (UniversalCover.proj x₀) ≃* FundamentalGroup X x₀`, "possibly up to `ᵐᵒᵖ`; pin the
action/composition convention first"). The theorem here is stated for an arbitrary regular
cover with simply connected total space, not as the specialized `UniversalCover.proj`
statement itself. That specialization is a later instantiation with `E = UniversalCover x₀`
once the corresponding regularity and simple-connectivity hypotheses are in scope.

The `ᵐᵒᵖ` is genuine and pins the convention noted in the roadmap. The deck group acts on
the total space on the *left* (`Deck.smul_eq_apply : φ • e = φ.1 e`), while the monodromy of
`π₁(X, x)` acts on each fibre on the *right* (`monodromy (γ.trans γ') = monodromy γ' ∘
monodromy γ`); choosing a basepoint lift `e` in the fibre and matching the deck element that
realises a monodromy therefore reverses multiplication, so the natural isomorphism lands in
`(Deck p)ᵐᵒᵖ`.

The isomorphism is Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv`, instantiated at
the group `Deck p` through `Deck.IsRegular.isQuotientCoveringMap`: a regular preconnected
covering exhibits its base as the quotient of the total space by `Deck p`, and for a simply
connected total space Mathlib's quotient-covering machinery identifies the deck group with
`π₁` of the base. As a corollary, choosing a basepoint lift `e` in the fibre over `x`
identifies `π₁(X, x)` with that fibre via monodromy.

## Main declarations

* `TauCeti.Deck.IsRegular.fundamentalGroupEquiv`: the anti-isomorphism
  `FundamentalGroup X x ≃* (Deck p)ᵐᵒᵖ`.
* `TauCeti.Deck.IsRegular.fundamentalGroupEquiv_unop_apply`: the deck element
  attached to `γ` moves the chosen lift `e` to `monodromy γ e`.
* `TauCeti.Deck.IsRegular.fundamentalGroupEquiv_apply_eq_iff`: characterizes equality
  with an arbitrary deck transformation by its value at the chosen lift.
* `TauCeti.Deck.IsRegular.fundamentalGroupEquiv_symm_monodromy`: characterizes the
  inverse equivalence by the monodromy translate of the chosen lift.
* `TauCeti.Deck.IsRegular.fundamentalGroupEquiv_eq_one_iff`: `γ` maps to the
  identity exactly when its monodromy fixes `e`.
* `TauCeti.Deck.IsRegular.fundamentalGroupDeckEquiv`: when the deck group is commutative,
  the opposite drops out and the fundamental group of the base is the deck group itself.

## References

The comparison map is Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv` (Junyan Xu,
`Mathlib/Topology/Homotopy/Lifting.lean`); the quotient-covering presentation of a regular
deck action is `TauCeti.Deck.IsRegular.isQuotientCoveringMap`.
-/

public section

namespace TauCeti

namespace Deck

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {x : X}

/-- For a regular covering map `p : E → X` with simply connected total space, the fundamental
group of the base is anti-isomorphic to the deck transformation group:
`FundamentalGroup X x ≃* (Deck p)ᵐᵒᵖ`. The `ᵐᵒᵖ` reflects that the deck group acts on the
left while the monodromy of `π₁` acts on the right; see the module docstring. -/
noncomputable def IsRegular.fundamentalGroupEquiv [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) :
    FundamentalGroup X x ≃* (Deck p)ᵐᵒᵖ :=
  (hreg.isQuotientCoveringMap hp).fundamentalGroupEquiv e

/-- The deck transformation attached to a loop class `γ` moves the chosen basepoint lift `e`
along the monodromy of `γ`. -/
@[simp]
lemma IsRegular.fundamentalGroupEquiv_unop_apply [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    (hreg.fundamentalGroupEquiv hp e γ).unop.1 (e : E) = (hp.monodromy γ e : E) :=
  (hreg.isQuotientCoveringMap hp).unop_fundamentalGroupToMulOpposite_smul

/-- Compatibility spelling of `fundamentalGroupEquiv_unop_apply` using the deck action. -/
lemma IsRegular.fundamentalGroupEquiv_unop_smul [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    (hreg.fundamentalGroupEquiv hp e γ).unop • (e : E) = hp.monodromy γ e := by
  simpa only [smul_eq_apply] using IsRegular.fundamentalGroupEquiv_unop_apply hreg hp e γ

/-- The fundamental group element `γ` corresponds to a deck transformation `g` exactly when
`g.unop` moves the chosen lift `e` to the monodromy translate of `e` along `γ`. -/
lemma IsRegular.fundamentalGroupEquiv_apply_eq_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (γ : FundamentalGroup X x) (g : (Deck p)ᵐᵒᵖ) :
    hreg.fundamentalGroupEquiv hp e γ = g ↔
      g.unop • (e : E) = hp.monodromy γ e :=
  (hreg.isQuotientCoveringMap hp).fundamentalGroupToMulOpposite_apply_eq_Iff

/-- The fundamental group element corresponding to an opposite deck transformation is the
unique loop class whose monodromy moves the chosen lift `e` by that deck transformation. -/
lemma IsRegular.fundamentalGroupEquiv_symm_monodromy [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (g : (Deck p)ᵐᵒᵖ) :
    (hp.monodromy ((hreg.fundamentalGroupEquiv hp e).symm g) e : E) = g.unop • (e : E) := by
  simpa using
    (IsRegular.fundamentalGroupEquiv_unop_apply hreg hp e
      ((hreg.fundamentalGroupEquiv hp e).symm g)).symm

/-- A `Deck p` spelling of `fundamentalGroupEquiv_symm_monodromy`. The loop class
corresponding to `MulOpposite.op φ` has monodromy action equal to `φ` at the chosen lift. -/
lemma IsRegular.fundamentalGroupEquiv_symm_op_monodromy [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (φ : Deck p) :
    (hp.monodromy ((hreg.fundamentalGroupEquiv hp e).symm (MulOpposite.op φ)) e : E) =
      φ • (e : E) := by
  simpa using IsRegular.fundamentalGroupEquiv_symm_monodromy hreg hp e (MulOpposite.op φ)

/-- A loop class `γ` maps to the identity deck transformation exactly when its monodromy
fixes the chosen basepoint lift `e`. -/
lemma IsRegular.fundamentalGroupEquiv_eq_one_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    hreg.fundamentalGroupEquiv hp e γ = 1 ↔ hp.monodromy γ e = e :=
  (hreg.isQuotientCoveringMap hp).fundamentalGroupToMulOpposite_eq_one_iff

/-- When the deck group of a regular covering map with simply connected total space is
**commutative**, the fundamental group of the base is the deck group itself: the opposite in
`IsRegular.fundamentalGroupEquiv` disappears because multiplication in the deck group
commutes. This is the form in which the comparison computes fundamental groups from deck
groups, e.g. `π₁(S¹) ≅ ℤ` (`TauCeti.AddCircle.fundamentalGroupMulEquiv`) and
`π₁(RPⁿ) ≅ ℤˣ` (`TauCeti.RealProjectiveSpace.fundamentalGroupMulEquiv`). -/
noncomputable def IsRegular.fundamentalGroupDeckEquiv [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ a b : Deck p, a * b = b * a) :
    FundamentalGroup X x ≃* Deck p :=
  (hreg.fundamentalGroupEquiv hp e).trans (MulOpposite.unopMulEquivOfComm hcomm)

/-- The deck transformation assigned to a loop class `γ`, in the commutative-deck-group form
of the comparison: it is the unopposite of `IsRegular.fundamentalGroupEquiv γ`. -/
@[simp]
lemma IsRegular.fundamentalGroupDeckEquiv_apply [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ a b : Deck p, a * b = b * a) (γ : FundamentalGroup X x) :
    hreg.fundamentalGroupDeckEquiv hp e hcomm γ =
      (hreg.fundamentalGroupEquiv hp e γ).unop := by
  simp [fundamentalGroupDeckEquiv]

/-- A loop class corresponds to the deck transformation `d`, in the commutative-deck-group
form of the comparison, exactly when `d` moves the chosen lift `e` to the monodromy translate
of `e` along `γ`. -/
lemma IsRegular.fundamentalGroupDeckEquiv_apply_eq_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ a b : Deck p, a * b = b * a)
    (γ : FundamentalGroup X x) (d : Deck p) :
    hreg.fundamentalGroupDeckEquiv hp e hcomm γ = d ↔ d • (e : E) = hp.monodromy γ e := by
  constructor
  · intro h
    subst h
    have key := (hreg.fundamentalGroupEquiv_apply_eq_iff hp e γ
      (hreg.fundamentalGroupEquiv hp e γ)).1 rfl
    rw [fundamentalGroupDeckEquiv_apply]
    exact key
  · intro h
    rw [fundamentalGroupDeckEquiv_apply]
    exact congrArg MulOpposite.unop
      ((hreg.fundamentalGroupEquiv_apply_eq_iff hp e γ (MulOpposite.op d)).2 h)

/-- The inverse equivalence sends a deck transformation to the unique loop class whose
monodromy moves the chosen lift by that transformation. -/
lemma IsRegular.fundamentalGroupDeckEquiv_symm_monodromy [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ a b : Deck p, a * b = b * a) (d : Deck p) :
    (hp.monodromy ((hreg.fundamentalGroupDeckEquiv hp e hcomm).symm d) e : E) = d • (e : E) :=
  ((hreg.fundamentalGroupDeckEquiv_apply_eq_iff hp e hcomm
    ((hreg.fundamentalGroupDeckEquiv hp e hcomm).symm d) d).1
      ((hreg.fundamentalGroupDeckEquiv hp e hcomm).apply_symm_apply d)).symm

/-- A loop class maps to the identity deck transformation exactly when its monodromy fixes
the chosen basepoint lift `e`. -/
lemma IsRegular.fundamentalGroupDeckEquiv_eq_one_iff [SimplyConnectedSpace E]
    (hreg : IsRegular p) (hp : IsCoveringMap p) (e : p ⁻¹' {x})
    (hcomm : ∀ a b : Deck p, a * b = b * a) (γ : FundamentalGroup X x) :
    hreg.fundamentalGroupDeckEquiv hp e hcomm γ = 1 ↔ hp.monodromy γ e = e := by
  rw [fundamentalGroupDeckEquiv_apply_eq_iff, one_smul]
  exact ⟨fun h => (Subtype.ext h).symm, fun h => (congrArg Subtype.val h).symm⟩

end Deck

end TauCeti
