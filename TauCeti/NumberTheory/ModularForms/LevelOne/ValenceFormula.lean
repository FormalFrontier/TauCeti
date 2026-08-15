/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.Order.AtCusp
public import TauCeti.NumberTheory.ModularForms.Order.OrbitReduction
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ValencePV

/-!
# The valence formula for level-one modular forms

The textbook valence formula, in orbit-sum form and with no hypothesis beyond `f ≠ 0`: for a
nonzero weight-`k` modular form on `SL₂(ℤ)`,

`ord_∞ f + 1/2 · ord_i f + 1/3 · ord_ρ f + ∑ (non-elliptic orbits q) ord_q f = k / 12`.

The proof assembles the two sides of the development. The contour side
(`FundamentalDomainBoundary/ValencePV.lean`) proves the identity for the divisor points of
any finite set capturing all zeros of the closed fundamental domain; instantiating it at the
canonical divisor set `fdZeros` discharges both capture hypotheses using `mem_fdZeros`. The
orbit side (`Order/OrbitReduction.lean`) rewrites the full non-elliptic orbit sum first as
the sum over the canonical left representatives and then as the three point-sum families —
strict interior, left vertical edge, left half-arc — which are literally the families of the
contour identity.

## Main declarations

* `valence_formula` (in `TauCeti.ModularForm`): the valence formula.

## References

The statement shape follows AINTLIB's `valence_formula_textbook_orbit_finsum`
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), commit `2baa76f742`,
Apache 2.0, `projects/LeanModularForms/LeanModularForms/ForMathlib/ValenceFormula.lean`),
with its `h_core` hypothesis discharged by the contour development rather than assumed.
-/

public section

open UpperHalfPlane

open scoped ModularForm MatrixGroups Modular

namespace TauCeti

namespace ModularForm

/-- **The valence formula** for weight-`k` modular forms on `SL₂(ℤ)`: for `f ≠ 0`, the cusp
order, the half-weighted order at `i`, the third-weighted order at `ρ` and the orders along
the non-elliptic orbits sum to `k / 12`. -/
theorem valence_formula {F : Type*} [FunLike F ℍ ℂ] {k : ℤ} [ModularFormClass F 𝒮ℒ k] (f : F)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ((∑ᶠ q : NonEllipticOrbit, orderOfVanishingOnOrbit f q.val : ℤ) : ℂ)
        + 1 / 2 * ((orderOfVanishingAt ⇑f UpperHalfPlane.I : ℤ) : ℂ)
        + 1 / 3 * ((orderOfVanishingAt ⇑f ρ : ℤ) : ℂ)
        + qExpansionOrderAtCusp 1 ⇑f = (k : ℂ) / 12 := by
  have hsplit : ((∑ᶠ q : NonEllipticOrbit, orderOfVanishingOnOrbit f q.val : ℤ) : ℂ) =
      ((∑ p ∈ (fdZeros f).filter (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2),
          orderOfVanishingAt ⇑f p
        + ∑ p ∈ (fdZeros f).filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖),
          orderOfVanishingAt ⇑f p
        + ∑ p ∈ (fdZeros f).filter
            (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
          orderOfVanishingAt ⇑f p : ℤ) : ℂ) := by
    exact_mod_cast (finsum_orderOfVanishingOnOrbit_eq_sum_canonicalReps f).trans
      (sum_canonicalReps_split f)
  have key := sum_orderOfVanishingAt_add_elliptic_add_qExpansionOrderAtCusp_eq
    f hf (S := fdZeros f) (fun p hp _ ↦ (mem_fdZeros.mp hp).1)
    (fun p hpfd hord ↦ mem_fdZeros.mpr ⟨hpfd, hord⟩)
  push_cast at hsplit key ⊢
  linear_combination hsplit + key

end ModularForm

end TauCeti

end
