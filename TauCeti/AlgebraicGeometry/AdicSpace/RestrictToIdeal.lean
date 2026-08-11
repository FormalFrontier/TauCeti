/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum
public import TauCeti.RingTheory.Valuation.CofinalIdeal.Restrict

/-!
# The restriction underlying the retraction `r_I`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §7.1.2.**

A point of `Spv A` is sent to the class of its canonical valuation restricted to `cΓ_v(I)`. The
restriction itself, together with its interface, lives in
`TauCeti.RingTheory.Valuation.CofinalIdeal.Restrict`; this file only carries it to the level of
points.

Wedhorn's retraction additionally **lands in** `Spv (A, I)` and **fixes** that subspace
pointwise; **neither is proved here**, so the map is stated with codomain `Spv A` rather than the
subspace, and is named for what it does — restriction to `I` — rather than for the retraction
property it does not yet carry.

## Main definitions

* `TauCeti.ValuationSpectrum.restrictToIdeal` : the restriction, at the level of points of
  `Spv A`.

## Main results

* `TauCeti.ValuationSpectrum.restrictToIdeal_def` : the point map, unfolded through the
  canonical valuation.
* `TauCeti.ValuationSpectrum.vle_restrictToIdeal` : the valuative relation of the restricted
  point, in terms of the original one.

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

end TauCeti.ValuationSpectrum
