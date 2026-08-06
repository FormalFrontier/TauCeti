/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic
public import TauCeti.NumberTheory.ModularForms.STransform

import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The arc self-pairing of the logarithmic-derivative integrand

The reflection `t ↦ 4 - t` carries the unit-circle arc of the boundary contour to its
own reversal through the inversion `S`. Composed with the `S`-transformation law of the
logarithmic derivative of a weight-`k` form, the reflected integrand
`logDeriv g (γ (4 - t)) · γ' (4 - t)` pairs with the direct one up to the weight term
`-k · γ' / γ` — so the two halves of the arc integral collapse to `-k` times the
integral of `γ' / γ`, whose integrand is `π/6 · i` on the open arc and hence almost
everywhere: the arc contributes `-k/12` to the `(2πi)⁻¹`-normalized valence contour,
the term that lands as `k/12` on the divisor side of the valence formula.

## Main declarations

* `TauCeti.ModularForm.logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg`: the
  direct and reflected arc contour integrands sum to the negated weight term.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/ArcContribution.lean`) this file ports
  onto the current Mathlib pin.
-/

public section

open Complex MeasureTheory Set UpperHalfPlane

open scoped MatrixGroups Real

namespace TauCeti

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- On the open arc, the direct and reflected logarithmic-derivative contour integrands
sum to the negated weight term `-k · logDeriv γ`. -/
theorem logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg
    [SlashInvariantFormClass F Γ k]
    (f : F) (hS : ModularGroup.S ∈ Γ) {H t : ℝ} (ht : t ∈ Ioo (1 : ℝ) 3)
    (hd : DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0) :
    deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t) +
      deriv (fdBoundary H) (4 - t) • logDeriv (⇑f ∘ ofComplex) (fdBoundary H (4 - t)) =
      -(k * logDeriv (fdBoundary H) t) := by
  have him := im_fdBoundary_arc_pos H ⟨ht.1.le, ht.2.le⟩
  have h0 : fdBoundary H t ≠ 0 := fun h ↦ absurd him (by simp [h])
  rw [fdBoundary_four_sub_arc H ⟨ht.1.le, ht.2.le⟩, deriv_fdBoundary_four_sub_arc H ht,
    smul_eq_mul, smul_eq_mul, logDeriv_comp_ofComplex_S_transform f hS him hd hne,
    logDeriv_apply (fdBoundary H) t]
  field_simp
  ring

end ModularForm

end TauCeti

end
