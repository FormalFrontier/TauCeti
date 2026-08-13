/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Lie.AdjointAction.Derivation

public section

/-!
# The inner automorphisms `exp (ad x)`

If `x` is an element of a Lie algebra `L` whose adjoint action `ad x` is nilpotent, then over a
base in which the factorials are invertible the finite sum `exp (ad x) = ∑ (i !)⁻¹ • (ad x)ⁱ` is an
automorphism of `L`. These are the generators of the group `Int L` of inner automorphisms, and they
are the Lie-algebra shadow of the root subgroups of a Chevalley group: for a root vector `e` of a
split semisimple Lie algebra, `exp (ad e)` is the adjoint action of `x_α(1)`.

Mathlib already exponentiates a nilpotent *derivation* (`LieDerivation.exp`) and knows that a root
vector is `ad`-nilpotent (`LieAlgebra.isNilpotent_ad_of_mem_rootSpace`). This file specialises the
first to the inner derivations `LieAlgebra.ad K L x` and records the truncations of the
exponential series that a hand computation needs: `TauCeti.expAd_apply_of_lie_eq_zero`,
`TauCeti.expAd_apply_of_lie_lie_eq_zero` and `TauCeti.expAd_apply_of_lie_lie_lie_eq_zero` evaluate
`exp (ad x)` on a vector killed by one, two or three brackets with `x`, which is every case that
occurs inside an `sl₂` triple.

## The `ℚ`-structure hypothesis

The exponential needs to divide by factorials, so `L` must be a `ℚ`-module. Following
`LieDerivation.exp`, this is carried by an unbundled `[LieAlgebra ℚ L]` hypothesis alongside the
base ring `K`. No compatibility between the two actions is assumed, and none is needed: an additive
group carries at most one `ℚ`-module structure, so the hypothesis names a structure rather than
choosing one (`Subsingleton (LieAlgebra ℚ L)`, in `Mathlib/Algebra/Lie/Basic.lean`). Where a
computation does mix the two scalar actions it goes through the `ℕ`-action that both refine, using
`Nat.cast_smul_eq_nsmul`. Whenever `K` is itself a `ℚ`-algebra — in particular whenever it is a
field of characteristic zero — such a structure exists: `TauCeti.ratLieAlgebra` builds it by
restricting scalars along `algebraMap ℚ K`.

## Main definitions

* `TauCeti.ratLieAlgebra`: the `ℚ`-Lie-algebra structure on a Lie algebra over a `ℚ`-algebra.
* `TauCeti.expAd`: the inner automorphism `exp (ad x)` of an `ad`-nilpotent element `x`.

## Main results

* `TauCeti.expAd_apply_eq_sum`: `exp (ad x)` is the truncated exponential series, truncated at any
  length that already annihilates the vector it is applied to.
* `TauCeti.expAd_apply_of_lie_eq_zero`, `TauCeti.expAd_apply_of_lie_lie_eq_zero`,
  `TauCeti.expAd_apply_of_lie_lie_lie_eq_zero`: the resulting one-, two- and three-term formulas.
* `TauCeti.expAd_apply_self`: `exp (ad x)` fixes `x`.

## References

* [J. Humphreys, *Introduction to Lie Algebras and Representation Theory*][humphreys1972], §2.3,
  where `Int L` is introduced.
* [R. W. Carter, *Simple Groups of Lie Type*][carter1972], §4.1.
-/

namespace TauCeti

open Finset LieAlgebra

/-- The `ℚ`-Lie-algebra structure on a Lie algebra `L` over a `ℚ`-algebra `K`, obtained by
restricting scalars along `algebraMap ℚ K`. A field of characteristic zero is such a `K`.

This is deliberately a `def` and not an `instance`: `K` cannot be recovered from the goal
`LieAlgebra ℚ L`, so instance search could never use it. It is what a consumer supplies with
`letI := TauCeti.ratLieAlgebra K L` in order to apply `TauCeti.expAd` and everything built on it,
and because `LieAlgebra ℚ L` is a subsingleton the choice is harmless. -/
@[instance_reducible]
noncomputable def ratLieAlgebra (K L : Type*) [CommRing K] [Algebra ℚ K] [LieRing L]
    [LieAlgebra K L] : LieAlgebra ℚ L :=
  letI : Module ℚ L := Module.compHom L (algebraMap ℚ K)
  -- by construction `q • y` *is* `algebraMap ℚ K q • y`, so `lie_smul` over `K` is the axiom asked
  { lie_smul := fun q x y ↦ lie_smul (algebraMap ℚ K q) x y }

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] [LieAlgebra ℚ L]

/-- The inner automorphism `exp (ad x)` attached to an element `x` with nilpotent adjoint action.
It is `LieDerivation.exp` applied to the inner derivation `ad x`. -/
noncomputable def expAd (x : L) (hx : IsNilpotent (ad K L x)) : L ≃ₗ⁅K⁆ L :=
  LieDerivation.exp (LieDerivation.ad K L x) <| by
    rwa [LieDerivation.coe_ad_apply_eq_ad_apply]

/-- `TauCeti.expAd` is the exponential of `LieAlgebra.ad x`. -/
lemma expAd_apply (x : L) (hx : IsNilpotent (ad K L x)) (y : L) :
    expAd x hx y = IsNilpotent.exp (ad K L x) y := by
  rw [expAd, LieDerivation.exp_map_apply, LieDerivation.coe_ad_apply_eq_ad_apply]

/-- The exponential series for `exp (ad x)`, truncated at any length `k` for which `(ad x) ^ k`
already annihilates the vector `y`. -/
lemma expAd_apply_eq_sum {x : L} (hx : IsNilpotent (ad K L x)) {k : ℕ} {y : L}
    (hy : ((ad K L x) ^ k) y = 0) :
    expAd x hx y = ∑ i ∈ range k, ((i.factorial : ℚ)⁻¹) • ((ad K L x) ^ i) y := by
  rw [expAd_apply]
  exact IsNilpotent.exp_smul_eq_sum (M := L) hy hx

/-- An element centralised by `x` is fixed by `exp (ad x)`. -/
lemma expAd_apply_of_lie_eq_zero {x y : L} (hx : IsNilpotent (ad K L x)) (hy : ⁅x, y⁆ = 0) :
    expAd x hx y = y := by
  rw [expAd_apply_eq_sum (k := 1) hx (by simpa using hy)]
  simp

/-- `exp (ad x)` fixes `x`. -/
@[simp]
lemma expAd_apply_self (x : L) (hx : IsNilpotent (ad K L x)) : expAd x hx x = x :=
  expAd_apply_of_lie_eq_zero hx (lie_self x)

/-- The two-term truncation of `exp (ad x)`, valid on a vector killed by two brackets with `x`. -/
lemma expAd_apply_of_lie_lie_eq_zero {x y : L} (hx : IsNilpotent (ad K L x))
    (hy : ⁅x, ⁅x, y⁆⁆ = 0) :
    expAd x hx y = y + ⁅x, y⁆ := by
  rw [expAd_apply_eq_sum (k := 2) hx (by simpa [pow_succ] using hy)]
  simp [Finset.sum_range_succ]

/-- The three-term truncation of `exp (ad x)`, valid on a vector killed by three brackets with
`x`. -/
lemma expAd_apply_of_lie_lie_lie_eq_zero {x y : L} (hx : IsNilpotent (ad K L x))
    (hy : ⁅x, ⁅x, ⁅x, y⁆⁆⁆ = 0) :
    expAd x hx y = y + ⁅x, y⁆ + (2⁻¹ : ℚ) • ⁅x, ⁅x, y⁆⁆ := by
  rw [expAd_apply_eq_sum (k := 3) hx (by simpa [pow_succ] using hy)]
  simp [Finset.sum_range_succ, pow_succ]

end TauCeti
