/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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

## The uniform form, and why it is the one general level needs

Singling out `i` and `ρ` is an artefact of level one, where those are the only two elliptic
points. The intrinsic statement weights *every* orbit by the reciprocal `1 / e_P` of its
elliptic order — the order of its `PSL(2, ℤ)`-stabiliser, `TauCeti.ModularGroup.ellipticOrder` —
and then reads

`∑_{P ∈ SL₂(ℤ) \ ℍ} (1 / e_P) · ord_P f + ord_∞ f = k / 12`,

with the `1/2` and the `1/3` produced by `e_i = 2` and `e_ρ = 3` and every other weight equal
to `1`. That is `valence_formula_weighted` below, stated over `ℚ` because the weights are
rational and the two sides are; the level-one shape above is the special case obtained by
splitting off the two orbits at which `e_P ≠ 1`.

The uniform shape is what the general-level formula of the Tau Ceti ModularForms roadmap's
Layer 1 milestone **"General level — by the coset norm"** consumes: there the level-one formula
is applied to the norm `∏_{γ ∈ Γ \ SL₂(ℤ)} f ∣[k] γ`, and each level-one weight `1 / e_P` is
redistributed over the `Γ`-orbits inside the `SL₂(ℤ)`-orbit of `P` by a stabiliser count. Only
in the uniform form is there a single weight per orbit to redistribute.

## Main declarations

* `valence_formula` (in `TauCeti.ModularForm`): the valence formula.
* `TauCeti.ModularForm.weightedOrderOfVanishingOnOrbit`: the summand `ord_P f / e_P` of its
  uniform form.
* `TauCeti.ModularForm.valence_formula_weighted`: the uniform form.
* `TauCeti.ModularForm.twelve_mul_orderOfVanishingOnOrbit_le_mul_ellipticOrder`: the resulting
  bound
  `12 · ord_P f ≤ k · e_P` on a single orbit, and
  `TauCeti.ModularForm.orderOfVanishingOnOrbit_eq_zero_of_weight_mul_ellipticOrder_lt_twelve`,
  the nonvanishing it forces when `k · e_P < 12`.

## References

The statement shape follows AINTLIB's `valence_formula_textbook_orbit_finsum`
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), commit `2baa76f742`,
Apache 2.0, `projects/LeanModularForms/LeanModularForms/ForMathlib/ValenceFormula.lean`),
with its `h_core` hypothesis discharged by the contour development rather than assumed.
The uniform form is the one displayed in the roadmap and follows the divisor-of-automorphic-forms
development in Diamond–Shurman, *A First Course in Modular Forms*, §§3.5–3.6.
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

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

/-! ### The uniform form, weighted by the elliptic orders -/

/-- **Splitting the uniform divisor sum at the two elliptic orbits.** Away from them the weight
is `1`, so the sum over all orbits is the non-elliptic sum of `valence_formula` plus the two
weighted elliptic terms. -/
lemma finsum_weightedOrderOfVanishingOnOrbit_eq [ModularFormClass F 𝒮ℒ k] (f : F) :
    (∑ᶠ q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ,
      weightedOrderOfVanishingOnOrbit f q) =
      ((∑ᶠ q : NonEllipticOrbit, orderOfVanishingOnOrbit f q.val : ℤ) : ℚ)
        + (orderOfVanishingAt ⇑f UpperHalfPlane.I : ℚ) / 2
        + (orderOfVanishingAt ⇑f ρ : ℚ) / 3 := by
  classical
  set S : Set (MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) :=
    {Quotient.mk'' UpperHalfPlane.I, Quotient.mk'' ρ} with hSdef
  have hmem : ∀ q, q ∈ Sᶜ ↔ (q ≠ Quotient.mk'' UpperHalfPlane.I ∧ q ≠ Quotient.mk'' ρ) := by
    intro q
    simp [hSdef, not_or]
  -- the two-element part contributes the weighted elliptic terms
  have hpair : (∑ᶠ q ∈ S, weightedOrderOfVanishingOnOrbit f q) =
      (orderOfVanishingAt ⇑f UpperHalfPlane.I : ℚ) / 2
        + (orderOfVanishingAt ⇑f ρ : ℚ) / 3 := by
    rw [hSdef, finsum_mem_pair ModularGroup.orbit_mk_I_ne_orbit_mk_ρ,
      weightedOrderOfVanishingOnOrbit_I, weightedOrderOfVanishingOnOrbit_ρ]
  -- the complement is the non-elliptic orbit type, on which the weight is trivial
  have hcompl : (∑ᶠ q ∈ Sᶜ, weightedOrderOfVanishingOnOrbit f q) =
      ((∑ᶠ q : NonEllipticOrbit, orderOfVanishingOnOrbit f q.val : ℤ) : ℚ) := by
    have hcast := AddMonoidHom.map_finsum_of_injective (Int.castAddHom ℚ) Int.cast_injective
      fun q : NonEllipticOrbit ↦ orderOfVanishingOnOrbit f q.val
    have hval : (∑ᶠ q ∈ Sᶜ, weightedOrderOfVanishingOnOrbit f q) =
        ∑ᶠ q ∈ Sᶜ, ((orderOfVanishingOnOrbit f q : ℤ) : ℚ) :=
      finsum_mem_congr rfl fun q hq ↦
        weightedOrderOfVanishingOnOrbit_of_orbit_ne_I_of_orbit_ne_ρ f
          ((hmem q).1 hq).1 ((hmem q).1 hq).2
    rw [hval, ← finsum_set_coe_eq_finsum_mem,
      ← finsum_comp_equiv (Equiv.subtypeEquivRight fun q ↦ (hmem q).symm)
        (f := fun q : (Sᶜ : Set _) ↦ ((orderOfVanishingOnOrbit f q.val : ℤ) : ℚ))]
    simpa using hcast.symm
  have hsplit := finsum_mem_add_sdiff' (f := weightedOrderOfVanishingOnOrbit f)
    (Set.subset_univ S)
    ((hasFiniteSupport_weightedOrderOfVanishingOnOrbit f).inter_of_right Set.univ)
  rw [finsum_mem_univ, ← Set.compl_eq_univ_sdiff, hpair, hcompl] at hsplit
  rw [← hsplit]
  ring

/-- **The valence formula, uniformly over the orbit space.** For a nonzero weight-`k` modular
form on `SL₂(ℤ)`, weighting each orbit by the reciprocal of its elliptic order,

`∑_{P ∈ SL₂(ℤ) \ ℍ} (1 / e_P) · ord_P f + ord_∞ f = k / 12`.

This is `valence_formula` with the two exceptional orbits absorbed into the general weight:
`e_i = 2` and `e_ρ = 3` restore the `1/2` and the `1/3`, and `e_P = 1` elsewhere makes every
other orbit count once. It is the form the general-level formula redistributes along the norm
map, where a single weight per orbit is what a stabiliser count can split. -/
theorem valence_formula_weighted [ModularFormClass F 𝒮ℒ k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ, weightedOrderOfVanishingOnOrbit f q)
      + (qExpansionOrderAtCusp 1 ⇑f : ℚ) = (k : ℚ) / 12 := by
  have key := valence_formula f hf
  rw [finsum_weightedOrderOfVanishingOnOrbit_eq f]
  refine Rat.cast_injective (α := ℂ) ?_
  push_cast
  linear_combination key

/-! ### Consequences for a single orbit -/

/-- **The mass at one orbit is bounded by the total mass**: every other term of the uniform
valence formula is nonnegative, so `12 · ord_P f ≤ k · e_P` for a nonzero form. -/
theorem twelve_mul_orderOfVanishingOnOrbit_le_mul_ellipticOrder
    [ModularFormClass F 𝒮ℒ k] (f : F)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ) :
    12 * orderOfVanishingOnOrbit f q ≤ k * ModularGroup.ellipticOrder q := by
  have hsingle := single_le_finsum q (hasFiniteSupport_weightedOrderOfVanishingOnOrbit f)
    (weightedOrderOfVanishingOnOrbit_nonneg f)
  have hcusp : (0 : ℚ) ≤ (qExpansionOrderAtCusp 1 ⇑f : ℚ) := by
    exact_mod_cast qExpansionOrderAtCusp_nonneg 1 ⇑f
  have htotal := valence_formula_weighted f hf
  have he : (0 : ℚ) < (ModularGroup.ellipticOrder q : ℚ) := by
    exact_mod_cast ModularGroup.ellipticOrder_pos q
  have hle : weightedOrderOfVanishingOnOrbit f q ≤ (k : ℚ) / 12 := by linarith
  rw [weightedOrderOfVanishingOnOrbit_def, div_le_div_iff₀ he (by norm_num)] at hle
  have : (12 : ℚ) * (orderOfVanishingOnOrbit f q : ℚ) ≤
      (k : ℚ) * (ModularGroup.ellipticOrder q : ℚ) := by linarith
  exact_mod_cast this

/-- **A small enough weighted degree forces nonvanishing at an orbit**: if `k · e_P < 12`, a
zero at `P` would make the single-orbit bound impossible. -/
theorem orderOfVanishingOnOrbit_eq_zero_of_weight_mul_ellipticOrder_lt_twelve
    [ModularFormClass F 𝒮ℒ k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    {q : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ}
    (hk : k * ModularGroup.ellipticOrder q < 12) :
    orderOfVanishingOnOrbit f q = 0 := by
  have hbound := twelve_mul_orderOfVanishingOnOrbit_le_mul_ellipticOrder f hf q
  have := orderOfVanishingOnOrbit_nonneg f q
  omega

end ModularForm

end TauCeti

end
