/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Koebe
public import Mathlib.Analysis.Calculus.Deriv.Basic
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

/-!
# The Riemann mapping theorem

Every simply connected open proper subset of `ℂ` is biholomorphic to the open unit disc.

## The proof, and where its parts live

The two halves are proved elsewhere, and this file only joins them:

* `ExtremalFamily.lean` maximizes `‖deriv f z₀‖` over the holomorphic injections of `Ω` into the
  disc that send a base point `z₀` to the origin, and shows by Montel and Hurwitz that the maximum
  is attained;
* `Koebe.lean` shows a maximizer omits no value of the disc, since a proper simply connected
  subdomain of the disc always admits a map with a larger derivative.

A maximizer is therefore injective, holomorphic and onto the disc, which is the theorem.

## Scope

This is **existence only**. Nothing here asserts uniqueness of the map, nor pins it down by a
normalization such as `f z₀ = 0` with `deriv f z₀ > 0` — although the map produced does satisfy the
first of those, being drawn from the pointed family.

The uniqueness companion is the sibling `Uniqueness.lean`, which shows two such maps differ by a
disc automorphism. It is independent of this file: it takes the biholomorphism onto the disc as a
hypothesis, where this file constructs one.

## Main statements

* `TauCeti.riemannMapping` — the theorem.
* `TauCeti.exists_bijOn_ball_differentiableOn_invFunOn` — the same map with a holomorphic inverse.

## Coordination with upstream Mathlib

The Riemann mapping theorem is being formalized upstream at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves the
L0–L3 prerequisites internally as private lemmas. The declarations here are an explicitly
**temporary shim**: delete them and refactor downstream consumers onto the exported Mathlib
versions once those land.

## References

* B. Riemann, *Grundlagen für eine allgemeine Theorie der Functionen einer veränderlichen complexen
  Grösse* (1851).
* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.
-/

public section

namespace TauCeti

open Complex Set Metric

/-- **The Riemann mapping theorem.** A simply connected open proper subset `Ω` of `ℂ` admits a
holomorphic bijection onto the open unit disc, with nonvanishing derivative throughout `Ω`.

Existence only: the map is not asserted to be unique, and no normalization is imposed. -/
theorem riemannMapping {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) :
    ∃ f : ℂ → ℂ, BijOn f Ω (ball 0 1) ∧ DifferentiableOn ℂ f Ω ∧ ∀ z ∈ Ω, deriv f z ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ := hΩc.nonempty
  obtain ⟨g, hg, hmax⟩ := exists_isMaxOn_norm_deriv_of_isSimplyConnected hΩc hΩo hΩ hz₀
  exact ⟨g, ⟨hg.mapsTo, hg.injOn, surjOn_ball_of_isMaxOn hΩo hΩc hz₀ hg hmax⟩,
    hg.differentiableOn, fun z hz => hg.deriv_ne_zero hΩo hz⟩

/-- **The Riemann mapping theorem as a biholomorphism.** The map of `TauCeti.riemannMapping` has a
holomorphic inverse: `Function.invFunOn f Ω` is holomorphic on the disc and inverts `f` on both
sides, so `Ω` and the disc are biholomorphic, not merely in holomorphic bijection.

Stated unbundled, in the idiom of `Set.BijOn` used throughout this development: the inverse is named
explicitly as `Function.invFunOn f Ω` rather than hidden inside a bundled equivalence, so a consumer
can rewrite with it directly. -/
theorem exists_bijOn_ball_differentiableOn_invFunOn {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩc : IsSimplyConnected Ω) (hΩ : Ω ≠ univ) :
    ∃ f : ℂ → ℂ, BijOn f Ω (ball 0 1) ∧ DifferentiableOn ℂ f Ω ∧
      DifferentiableOn ℂ (Function.invFunOn f Ω) (ball 0 1) ∧
      LeftInvOn (Function.invFunOn f Ω) f Ω ∧
      RightInvOn (Function.invFunOn f Ω) f (ball 0 1) := by
  obtain ⟨f, hbij, hfd, -⟩ := riemannMapping hΩo hΩc hΩ
  refine ⟨f, hbij, hfd, ?_, hbij.injOn.leftInvOn_invFunOn, hbij.surjOn.rightInvOn_invFunOn⟩
  -- Dot notation would resolve to `Function.invFunOn`; name the lemma explicitly.
  have hinv := TauCeti.DifferentiableOn.invFunOn hfd hΩo hbij.injOn
  rwa [hbij.image_eq] at hinv

end TauCeti
