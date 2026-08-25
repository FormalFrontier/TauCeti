/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import TauCeti.RingTheory.IntegralClosure.Quotient
import TauCeti.RingTheory.Valuation.ValuativeRel.Comap

/-!
# The valuative criterion for integrality

If every valuation of `R` that is bounded by `1` on a subring `B` is also bounded by `1` at
`x`, then `x` is integral over `B`.

This is the hard direction of the correspondence Wedhorn records as Proposition 7.18, for
which he gives only the citation [Hu2, Lemma 3.3]. It is the substantial ingredient of the
comparison between two presentations of a rational subset, which Layer 3.1 of the roadmap
asks for and which `presentationRingEquiv` currently takes as a hypothesis.

## Method

The proof has two steps, and `R` is an arbitrary commutative ring in the statement.

For a **domain** the argument is by contraposition through the fraction field. If `x` is not
integral over `B` then its image is outside the integral closure of `B` in `Frac R`, so
`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn` — the Stacks project's 090P(1) —
produces a valuation subring `V` containing that closure and missing the image of `x`.
Pulling `V.valuation` back along the inclusion gives a valuation of `R` bounded by `1` on `B`
but not at `x`, contradicting the hypothesis.

Routing through `Frac R` needs `R` to be a domain, which is a hypothesis Wedhorn's statement
does not carry. It is removed by **reducing modulo a prime**: by
`TauCeti.isIntegral_of_forall_isPrime_map` it is enough to be integral over the image of `B` in
`R ⧸ J` for every prime `J`, and each `R ⧸ J` is a domain, so the domain case applies there. Its
hypothesis is met because a valuation of `R ⧸ J` pulls back along `Ideal.Quotient.mk J`, by
`TauCeti.ValuativeRel.comap`, to one of `R`, which the hypothesis on `R` bounds. So the criterion
holds for `R` in general.

## Main results

* `TauCeti.isIntegral_of_forall_valuation_le_one`: the criterion.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.18, stated
  there with the proof given as the citation [Hu2, Lemma 3.3].
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), commit `37bbdaeb9`,
  `projects/AdicSpaces/Adic spaces/Presheaf.lean`, `isIntegral_of_forall_valuation_le_one` — the
  proof route followed in the domain step. **Adapted, not copied**: that declaration carries an
  openness hypothesis its own underscore marks as unused, so the topology is dropped and the
  statement here is purely algebraic, which is why this file sits under `RingTheory/Valuation/`.
  It also assumes `[IsDomain R]`, as every version of this criterion in that development does;
  the reduction to a prime quotient that removes the hypothesis has no counterpart there.
-/

public section

namespace TauCeti

open _root_.ValuativeRel

/-- `ValuativeRel.ofValuation v` compares by `v`: this is how the relation is defined, and the
only step of the proof below that is definitional rather than lemma-driven. Naming it confines
that unfolding to one place; the `comap` layer goes through `Valuation.comap_apply` instead. -/
private theorem vle_ofValuation {S Γ : Type*} [Ring S] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation S Γ) (x y : S) : (ofValuation v).vle x y ↔ v x ≤ v y := Iff.rfl

/-- **The valuative criterion for integrality, for a domain.** This is the step of
`isIntegral_of_forall_valuation_le_one` that passes through `Frac R`; the general statement is
reduced to it modulo a prime ideal, so it is not part of the interface. -/
private theorem isIntegral_of_forall_valuation_le_one_of_isDomain {R : Type*} [CommRing R]
    [IsDomain R] {B : Subring R} {x : R}
    (hvle : ∀ v : ValuativeRel R, (∀ b ∈ B, v.vle b 1) → v.vle x 1) : IsIntegral B x := by
  by_contra hni
  -- pass to the fraction field; `x` stays non-integral because the map is injective, which
  -- `isIntegral_algebraMap_iff` now draws from the `FaithfulSMul` instance rather than a
  -- hypothesis
  let i := algebraMap R (FractionRing R)
  have hxni : i x ∉ (integralClosure B (FractionRing R)).toSubring := by
    rw [Subalgebra.mem_toSubring, mem_integralClosure_iff]
    exact mt isIntegral_algebraMap_iff.mp hni
  -- Stacks 090P(1): a valuation subring containing the closure but missing `i x`
  obtain ⟨V, hVle, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hxni
  -- `vle` for the pulled-back relation is the valuation inequality: `vle_ofValuation` for the
  -- relation and `Valuation.comap_apply` for the pullback, rather than one `Iff.rfl` across both
  have hvle_iff : ∀ y z : R, (ofValuation (V.valuation.comap i)).vle y z ↔
      V.valuation (i y) ≤ V.valuation (i z) := fun y z ↦ by
    rw [vle_ofValuation, Valuation.comap_apply, Valuation.comap_apply]
  -- pull `V.valuation` back to `R`; it is `≤ 1` on `B`
  have hB : ∀ b ∈ B, (ofValuation (V.valuation.comap i)).vle b 1 := by
    intro b hb
    rw [hvle_iff]
    simp only [map_one, ValuationSubring.valuation_le_one_iff]
    exact hVle (Subalgebra.algebraMap_mem (integralClosure B (FractionRing R)) ⟨b, hb⟩)
  -- the hypothesis then puts `i x` in `V`, which is the contradiction
  refine hxV ?_
  rw [← V.valuation_le_one_iff]
  simpa only [map_one] using (hvle_iff x 1).mp (hvle _ hB)

/-- **The valuative criterion for integrality.** If `v x ≤ 1` for every valuation `v` of `R`
satisfying `v b ≤ 1` for all `b ∈ B`, then `x` is integral over `B`.

This is the hard direction of Wedhorn's Proposition 7.18, for an arbitrary commutative ring —
the generality he states it in. The proof of the domain case goes through `Frac R`, and the
general case is reduced to it by `isIntegral_of_forall_isPrime_map`, which asks only that `x`
become integral in every prime quotient. -/
theorem isIntegral_of_forall_valuation_le_one {R : Type*} [CommRing R] {B : Subring R} {x : R}
    (hvle : ∀ v : ValuativeRel R, (∀ b ∈ B, v.vle b 1) → v.vle x 1) : IsIntegral B x := by
  -- it is enough to be integral in each prime quotient, and `R ⧸ J` is then a domain
  refine isIntegral_of_forall_isPrime_map fun J hJ ↦
    isIntegral_of_forall_valuation_le_one_of_isDomain fun w hw ↦ ?_
  -- No `ValuativeRel` instance on `R ⧸ J` is installed, and none is needed: the domain case
  -- quantifies over every `w : ValuativeRel (R ⧸ J)`, so the relation arrives here as a bound
  -- variable. An instance would in any case be an arbitrary global choice, since a quotient of a
  -- ring carries no canonical valuation relation.
  -- a valuation of `R ⧸ J` bounded on the image of `B` pulls back to one bounded on `B`
  have hB : ∀ b ∈ B, (ValuativeRel.comap (Ideal.Quotient.mk J) w).vle b 1 := by
    intro b hb
    rw [ValuativeRel.comap_vle, map_one]
    exact hw _ (Subring.mem_map.2 ⟨b, hb, rfl⟩)
  simpa only [ValuativeRel.comap_vle, map_one] using hvle _ hB

end TauCeti
