/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

end Deck

end TauCeti
