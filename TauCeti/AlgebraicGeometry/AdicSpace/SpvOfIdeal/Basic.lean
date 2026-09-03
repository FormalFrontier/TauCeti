/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum
public import TauCeti.RingTheory.Valuation.CofinalIdeal.Greatest

/-!
# The subspace `Spv (A, I)` of the valuation spectrum

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §7.1.1.** For an ideal `I` satisfying the
standing hypothesis of §7.1 — that `I` has the same radical as some finitely generated ideal —
Wedhorn carves out of the valuation spectrum the set

```text
Spv (A, I) = { v ∈ Spv A : cΓ_v(I) = Γ_v }
```

of points whose ideal-indexed characteristic subgroup is everything.

Points of `Spv A` are *classes* of valuations, so a condition on valuations cuts out a subset
only if it is class-invariant. That is Lemma 7.4's role, recorded as
`Valuation.characteristicSubgroupOfIdeal_eq_top_congr_of_isEquiv`. No quotient
eliminator is needed: `ValuationSpectrum.valuation` picks a canonical representative of each
point and `ofValuation_valuation` says the choice round-trips, so the set is defined directly
by that representative and `mem_spvOfIdeal_ofValuation` transfers the test to any other.

## Relation to the AINTLIB formalisation

The AINTLIB adic-spaces development (`aintlib-adic-spaces`, revision `37bbdaeb9`,
`projects/AdicSpaces/Adic spaces/SpvAI.lean`) already formalises this space, as
`Spv.IsInSpvAI`, but by the *other* clause of Lemma 7.4:

```text
(∀ a ∈ I, Valuation.CofinalValue v a) ∨ Valuation.IsMicrobial v
```

Taking clause (ii) as the definition sidesteps `cΓ_v(I)` entirely, so that development needs
neither Lemma 7.2 nor Definition 7.3. This file instead takes clause (i), `cΓ_v(I) = Γ_v`, as
Wedhorn does in §7.1.1, and recovers the disjunctive form as a theorem:
`mem_spvOfIdeal_iff_forall_cofinalValue_or_characteristicSubgroup_eq_top`
is essentially AINTLIB's definition, proved rather than assumed. The two routes agree by
Lemma 7.4.

## Main definitions

* `TauCeti.ValuationSpectrum.spvOfIdeal` : the subset `Spv (A, I)` of `Spv A`.

## Main results

* `mem_spvOfIdeal_iff_forall_cofinalValue_or_characteristicSubgroup_eq_top` : **Lemma 7.4**
  at the `Spv` level — the criterion in the form a consumer can actually check.
* `TauCeti.ValuationSpectrum.mem_spvOfIdeal_iff` : membership unfolded through the canonical
  valuation, and `TauCeti.ValuationSpectrum.mem_spvOfIdeal_ofValuation` : membership tested on
  an arbitrary representative, which is what makes the definition usable.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1.1 and Lemma 7.4
-/

public section

namespace TauCeti.ValuationSpectrum

open Valuation MonoidWithZeroHom

variable {A : Type*} [CommRing A]

/-- **Wedhorn §7.1.1.** The subspace `Spv (A, I)` of the valuation spectrum: the points whose
ideal-indexed characteristic subgroup `cΓ_v(I)` is the whole value group. The hypothesis `hfg`
is Wedhorn's standing assumption for §7.1, that `I` shares a radical with a finitely generated
ideal; it is what makes `cΓ_v(I)` well posed. -/
def spvOfIdeal (I : Ideal A) (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    Set (Spv A) :=
  {v | characteristicSubgroupOfIdeal v.valuation I hfg = ⊤}

-- Not `@[simp]`: its right-hand side rewrites the left-hand side of the `@[simp]` lemma
-- `mem_spvOfIdeal_ofValuation` below, leaving that sibling outside simp-normal form, which
-- `simpNF` rejects.
/-- Membership in `Spv (A, I)`, unfolded through the canonical valuation of the point. The
usable form is `mem_spvOfIdeal_ofValuation`, which tests an arbitrary representative. -/
theorem mem_spvOfIdeal_iff {I : Ideal A} {hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical}
    {v : Spv A} :
    v ∈ spvOfIdeal I hfg ↔ characteristicSubgroupOfIdeal v.valuation I hfg = ⊤ :=
  Iff.rfl

/-- **Membership is testable on any representative.** The defining condition is stated through
the canonical valuation of a point, but any valuation representing that point gives the same
answer. -/
@[simp]
theorem mem_spvOfIdeal_ofValuation {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    ofValuation w ∈ spvOfIdeal I hfg ↔ characteristicSubgroupOfIdeal w I hfg = ⊤ :=
  characteristicSubgroupOfIdeal_eq_top_congr_of_isEquiv (isEquiv_valuation_ofValuation w) hfg

/-- **The criterion, in checkable form (Wedhorn Lemma 7.4).** A point lies in `Spv (A, I)`
exactly when every element of `I` has cofinal value, or the characteristic subgroup is already
everything. Stated at the level of `Spv A`, so consumers need not reach for
`characteristicSubgroupOfIdeal`. -/
theorem mem_spvOfIdeal_iff_forall_cofinalValue_or_characteristicSubgroup_eq_top {I : Ideal A}
    {hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical} {v : Spv A} :
    v ∈ spvOfIdeal I hfg ↔
      (∀ a ∈ I, CofinalValue v.valuation a) ∨ characteristicSubgroup v.valuation = ⊤ :=
  characteristicSubgroupOfIdeal_eq_top_iff hfg

end TauCeti.ValuationSpectrum
