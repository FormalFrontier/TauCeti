/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Lie.AdjointAction.Basic
public import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Algebra.Ring.Action.ConjAct
import TauCeti.Algebra.Ring.Commutator

public section

/-!
# The inner automorphisms `exp (ad x)`

If `x` is an element of a Lie algebra `L` whose adjoint action `ad x` is nilpotent, then over a
base in which the factorials are invertible the finite sum `exp (ad x) = ∑ (i !)⁻¹ • (ad x)ⁱ` is an
automorphism of `L`. These are the generators of the group `Int L` of inner automorphisms, and they
are the Lie-algebra shadow of the root subgroups of a Chevalley group: for a root vector `e` of a
split semisimple Lie algebra, `exp (ad e)` is the adjoint action of `x_α(1)`.

For an element `x` of an associative `ℚ`-algebra, this shadow is identified with the actual
conjugation action of the nilpotent exponential:

```text
exp (ad x) y = exp(x) y exp(-x).
```

As an application, if `[x, y] = z` and `z` commutes with both `x` and `y`, then

```text
exp(x) exp(y) = exp(y) exp(z) exp(x).
```

This is the central-commutator case of the Chevalley commutator formula. It is the relation for an
`A₂` pair of root vectors and is also a building block for the longer rank-two formulas.

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
* `TauCeti.expAd_apply_eq_exp_mul_exp_neg`: on an associative algebra, `exp (ad x)` is
  conjugation by `exp x`.
* `TauCeti.exp_mul_exp_eq_exp_mul_exp_mul_of_lie_eq_of_commute`: the exponential relation for a
  central commutator.

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

/-! ## Conjugation by nilpotent exponentials -/

section Associative

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- In an associative `ℚ`-algebra, the inner automorphism `exp (ad x)` is conjugation by the
nilpotent exponential `exp x`.

The inverse of `exp x` is written explicitly as `exp (-x)`. This form is the bridge between the
Lie-algebra automorphisms above and root subgroup elements in a Chevalley group. -/
@[simp]
theorem expAd_apply_eq_exp_mul_exp_neg {x y : A} (hx : IsNilpotent x) :
    expAd (K := ℚ) x (LieAlgebra.ad_nilpotent_of_nilpotent (R := ℚ) hx) y =
      IsNilpotent.exp x * y * IsNilpotent.exp (-x) := by
  rw [expAd_apply, LieAlgebra.ad_eq_lmul_left_sub_lmul_right (R := ℚ)]
  have hleft : IsNilpotent (LinearMap.mulLeft ℚ x) := by
    rwa [LinearMap.isNilpotent_mulLeft_iff]
  have hright : IsNilpotent (LinearMap.mulRight ℚ x) := by
    rwa [LinearMap.isNilpotent_mulRight_iff]
  have had : ((LinearMap.mulLeft ℚ : A → Module.End ℚ A) -
        (LinearMap.mulRight ℚ : A → Module.End ℚ A)) x =
      LinearMap.mulLeft ℚ x - LinearMap.mulRight ℚ x := rfl
  rw [had, sub_eq_add_neg, IsNilpotent.exp_add_of_commute
    ((LinearMap.commute_mulLeft_right x x).neg_right) hleft hright.neg]
  have hl := IsNilpotent.map_exp hx (Algebra.lsmul ℚ ℚ A)
  have hxop : IsNilpotent (MulOpposite.op (-x)) := hx.neg.op
  let rsmul : Aᵐᵒᵖ →ₐ[ℚ] Module.End ℚ A := Algebra.lsmul ℚ ℚ A
  have hr := IsNilpotent.map_exp hxop rsmul
  have hmulLeft : (Algebra.lsmul ℚ ℚ A) x = LinearMap.mulLeft ℚ x := by
    ext a
    simp [Algebra.lsmul_apply, LinearMap.mulLeft_apply]
  have hmulRight : rsmul (MulOpposite.op (-x)) = LinearMap.mulRight ℚ (-x) := by
    ext a
    rw [Algebra.lsmul_apply, op_smul_eq_mul, LinearMap.mulRight_apply]
  have hexpOp : MulOpposite.unop (IsNilpotent.exp (MulOpposite.op (-x))) =
      IsNilpotent.exp (-x) := by
    obtain ⟨k, hk⟩ := hx.neg
    have hk_op : MulOpposite.op (-x) ^ k = 0 := by
      rw [← MulOpposite.op_pow, hk, MulOpposite.op_zero]
    rw [IsNilpotent.exp_eq_sum hk, IsNilpotent.exp_eq_sum hk_op]
    simp
  have hl' (a : A) : IsNilpotent.exp (LinearMap.mulLeft ℚ x) a =
      IsNilpotent.exp x * a := by
    rw [← hmulLeft]
    simpa [Algebra.smul_def] using LinearMap.congr_fun hl.symm a
  have hr' (a : A) : IsNilpotent.exp (LinearMap.mulRight ℚ (-x)) a =
      a * IsNilpotent.exp (-x) := by
    calc
      IsNilpotent.exp (LinearMap.mulRight ℚ (-x)) a =
          IsNilpotent.exp (rsmul (MulOpposite.op (-x))) a := by rw [hmulRight]
      _ = rsmul (IsNilpotent.exp (MulOpposite.op (-x))) a :=
        LinearMap.congr_fun hr.symm a
      _ = (IsNilpotent.exp (MulOpposite.op (-x))) • a :=
        Algebra.lsmul_apply (R := ℚ) (B := ℚ) (M := A) (IsNilpotent.exp (MulOpposite.op (-x))) a
      _ = a * MulOpposite.unop (IsNilpotent.exp (MulOpposite.op (-x))) :=
        MulOpposite.smul_eq_mul_unop _ _
      _ = a * IsNilpotent.exp (-x) := by rw [hexpOp]
  have hnegRight : -(LinearMap.mulRight ℚ x) = LinearMap.mulRight ℚ (-x) := by
    ext a
    simp
  rw [Module.End.mul_apply, hnegRight, hr', hl']
  exact (mul_assoc _ _ _).symm

private theorem exp_mul_exp_mul_exp_neg {x y : A} (hx : IsNilpotent x)
    (hy : IsNilpotent y) :
    IsNilpotent.exp x * IsNilpotent.exp y * IsNilpotent.exp (-x) =
      IsNilpotent.exp
        (expAd (K := ℚ) x (LieAlgebra.ad_nilpotent_of_nilpotent (R := ℚ) hx) y) := by
  let u : Aˣ :=
    { val := IsNilpotent.exp x
      inv := IsNilpotent.exp (-x)
      val_inv := IsNilpotent.exp_mul_exp_neg_self hx
      inv_val := IsNilpotent.exp_neg_mul_exp_self hx }
  let e : A →+* A :=
    MulSemiringAction.toRingHom (ConjAct Aˣ) A (ConjAct.toConjAct u)
  have he (a : A) : e a = IsNilpotent.exp x * a * IsNilpotent.exp (-x) := by
    rw [MulSemiringAction.toRingHom_apply, ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
    rfl
  have hmap := IsNilpotent.map_exp hy e
  calc
    IsNilpotent.exp x * IsNilpotent.exp y * IsNilpotent.exp (-x) =
        e (IsNilpotent.exp y) := (he (IsNilpotent.exp y)).symm
    _ = IsNilpotent.exp (e y) := hmap
    _ = IsNilpotent.exp
        (expAd (K := ℚ) x (LieAlgebra.ad_nilpotent_of_nilpotent (R := ℚ) hx) y) := by
      rw [expAd_apply_eq_exp_mul_exp_neg hx, he]

/-- **The central-commutator exponential relation.** If `[x, y] = z`, the element `z` commutes
with `x` and `y`, and `x` and `y` are nilpotent, then
`exp(x) exp(y) = exp(y) exp(z) exp(x)`.

For root vectors whose roots form an `A₂` pair, this is the Chevalley commutator relation. The
hypotheses are stated for arbitrary elements of an associative `ℚ`-algebra so the result also
applies directly to their images in finite-dimensional representations. -/
theorem exp_mul_exp_eq_exp_mul_exp_mul_of_lie_eq_of_commute {x y z : A}
    (hxy : ⁅x, y⁆ = z) (hxz : Commute x z) (hyz : Commute y z)
    (hx : IsNilpotent x) (hy : IsNilpotent y) :
    IsNilpotent.exp x * IsNilpotent.exp y =
      IsNilpotent.exp y * IsNilpotent.exp z * IsNilpotent.exp x := by
  have hz : IsNilpotent z :=
    Associative.isNilpotent_of_commutator_eq (by rw [← hxy, Ring.lie_def]; abel) hxz hyz hx
  have hconj : IsNilpotent.exp x * IsNilpotent.exp y * IsNilpotent.exp (-x) =
      IsNilpotent.exp y * IsNilpotent.exp z := by
    rw [exp_mul_exp_mul_exp_neg hx hy,
      expAd_apply_of_lie_lie_eq_zero
        (LieAlgebra.ad_nilpotent_of_nilpotent (R := ℚ) hx) (by rw [hxy]; exact hxz.lie_eq),
      hxy, IsNilpotent.exp_add_of_commute hyz hy hz]
  calc
    IsNilpotent.exp x * IsNilpotent.exp y =
        (IsNilpotent.exp x * IsNilpotent.exp y * IsNilpotent.exp (-x)) *
          IsNilpotent.exp x := by
            rw [mul_assoc, IsNilpotent.exp_neg_mul_exp_self hx, mul_one]
    _ = IsNilpotent.exp y * IsNilpotent.exp z * IsNilpotent.exp x := by rw [hconj]

end Associative

end TauCeti
