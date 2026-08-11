/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.SpvOfIdeal
public import TauCeti.RingTheory.Valuation.CofinalIdeal.Restrict

/-!
# The restriction underlying the retraction `r_I`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §7.1.2.**

A point of `Spv A` is sent to the class of its canonical valuation restricted to `cΓ_v(I)`. The
restriction itself, together with its interface, lives in
`TauCeti.RingTheory.Valuation.CofinalIdeal.Restrict`; this file only carries it to the level of
points.

Wedhorn's retraction has two properties beyond being this map: it **lands in** `Spv (A, I)`, and
it **fixes** that subspace pointwise. The first is proved here, and the map is therefore also
offered with the codomain the roadmap asks for, as `restrictToIdealCodRestrict`. The second is
not proved here, so neither form is called `retract`: both are named for what they are shown to
do — restriction to `I` — rather than for the retraction property still outstanding.

## Main definitions

* `TauCeti.ValuationSpectrum.restrictToIdeal` : the restriction, at the level of points of
  `Spv A`.
* `TauCeti.ValuationSpectrum.restrictToIdealCodRestrict` : the same map with the roadmap's
  codomain, `Spv A → Spv (A, I)`, obtained by corestricting along the landing theorem below. This
  is the canonical form for a consumer, who then holds a point of the subspace rather than a
  point of `Spv A` together with a membership proof.

## Main results

* `TauCeti.ValuationSpectrum.restrictToIdeal_def` : the point map, unfolded through the
  canonical valuation.
* `TauCeti.ValuationSpectrum.vle_restrictToIdeal` : the valuative relation of the restricted
  point, in terms of the original one.
* `TauCeti.ValuationSpectrum.restrictToIdeal_mem_spvOfIdeal` : the restriction lands in
  `Spv (A, I)`. The mathematics is valuation-level and proved there, as
  `TauCeti.Valuation.characteristicSubgroupOfIdeal_restrictToIdeal_eq_top`; this only adds that
  membership may be tested on the canonical valuation of the point.
* `TauCeti.ValuationSpectrum.coe_restrictToIdealCodRestrict` : the corestriction read back in
  `Spv A`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1.2
-/

public section

namespace TauCeti.ValuationSpectrum

open MonoidWithZeroHom TauCeti TauCeti.Valuation

variable {A : Type*} [CommRing A]

/-- **The underlying map of Wedhorn's §7.1.2 retraction.** A point of `Spv A` is sent to the
class of its canonical valuation restricted to `cΓ_v(I)`. -/
noncomputable def restrictToIdeal (v : Spv A) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) : Spv A :=
  ofValuation (v.valuation.restrictToIdeal I hfg)

/-- **The point map, unfolded through the canonical valuation.** Consumers rewrite through this
to reach the valuation-level restriction rather than unfolding the definition, whose body is not
exposed. Note this is the definitional unfolding at `v.valuation`, not a formula valid at an
arbitrary representative of the class. -/
theorem restrictToIdeal_def (v : Spv A) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    restrictToIdeal v I hfg = ofValuation (v.valuation.restrictToIdeal I hfg) :=
  (rfl)

/-- **The valuative relation of the restricted point.** Comparison is the whole observable
content of a point of `Spv A`, so this is the interface to `restrictToIdeal` at the level of
points: `a ≤ b` after restriction exactly when `a`'s value is discarded, or `b`'s is kept and
`a ≤ b` held already. The side conditions are discharged by
`TauCeti.Valuation.restrictToIdeal_eq_zero_iff`. -/
@[simp]
theorem vle_restrictToIdeal (v : Spv A) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (a b : A) :
    (restrictToIdeal v I hfg).toValuativeRel.vle a b ↔
      v.valuation.restrictToIdeal I hfg a = 0 ∨
        v.valuation.restrictToIdeal I hfg b ≠ 0 ∧ v.toValuativeRel.vle a b := by
  rw [restrictToIdeal_def, vle_ofValuation, TauCeti.Valuation.restrictToIdeal_le_iff]
  exact or_congr_right (and_congr_right fun _ ↦ valuation_le_iff v a b)

/-- **Wedhorn §7.1.2: the restriction lands in `Spv (A, I)`.** This is the substantive half of
the roadmap's `r_I : Spv A → Spv (A, I)`: the point `restrictToIdeal v I` really does satisfy the
condition cutting out the subspace.

The mathematics is valuation-level and lives there, as
`TauCeti.Valuation.characteristicSubgroupOfIdeal_restrictToIdeal_eq_top`; all this adds is that
membership of a point may be tested on its canonical valuation. -/
@[simp]
theorem restrictToIdeal_mem_spvOfIdeal (v : Spv A) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    restrictToIdeal v I hfg ∈ spvOfIdeal I hfg := by
  rw [restrictToIdeal_def, mem_spvOfIdeal_ofValuation]
  exact TauCeti.Valuation.characteristicSubgroupOfIdeal_restrictToIdeal_eq_top _ I hfg

/-- **The roadmap's `r_I : Spv A → Spv (A, I)`**, with the codomain the roadmap asks for. This is
`restrictToIdeal` corestricted along the landing theorem, so a consumer receives a point of the
subspace rather than an `Spv A`-point plus a membership proof to carry around.

It is named for the restriction rather than for a retraction: that it *is* a retraction needs the
second law — that it fixes `Spv (A, I)` pointwise — which is proved separately. -/
noncomputable def restrictToIdealCodRestrict (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (v : Spv A) :
    (spvOfIdeal I hfg : Set (Spv A)) :=
  ⟨restrictToIdeal v I hfg, restrictToIdeal_mem_spvOfIdeal v I hfg⟩

/-- The corestricted map is the plain one, read in `Spv A`. -/
@[simp]
theorem coe_restrictToIdealCodRestrict (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (v : Spv A) :
    (restrictToIdealCodRestrict I hfg v : Spv A) = restrictToIdeal v I hfg :=
  (rfl)

end TauCeti.ValuationSpectrum
