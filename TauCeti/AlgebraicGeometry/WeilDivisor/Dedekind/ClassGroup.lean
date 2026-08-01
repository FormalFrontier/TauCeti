/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor.Basic

/-!
# The divisor class group of a Dedekind domain is its ideal class group

For a Dedekind domain `R` with fraction field `K`,
`TauCeti.AlgebraicGeometry.WeilDivisor.Dedekind.Basic` packages the height-one spectrum of `R` as
the points of an affine curve and the order of vanishing of a rational function as the order system
`OrderSystem.ofDedekindDomain R K`; its class group `(OrderSystem.ofDedekindDomain R K).ClassGroup`
is the free Weil-divisor group on the height-one primes modulo principal divisors.
`TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor.Basic` adds the Cartier side, the
isomorphism `fractionalIdealDivisorAddEquiv` between invertible fractional ideals and Weil divisors,
and records that it carries principal fractional ideals to principal divisors. Both files explicitly
leave the **quotient-level** comparison open. This file supplies it.

The isomorphism `fractionalIdealDivisorAddEquiv R K` sends the subgroup of principal fractional
ideals `(toPrincipalIdeal R K).range` onto the subgroup of principal divisors, so it descends to
an isomorphism of quotients

`classGroupAddEquiv : (OrderSystem.ofDedekindDomain R K).ClassGroup ≃+ Additive (ClassGroup R)`,

the Weil-divisor divisor class group of the affine Dedekind curve identified with Mathlib's ideal
class group `ClassGroup R`. It is characterized by sending the class of the Weil divisor of an
invertible fractional ideal `I` to the ideal class of `I`, and its inverse sends the ideal class
of `I` back to the divisor class of the divisor of `I`; in particular the class of the point
divisor `[v]` of a height-one prime `v` is the ideal class of `v`.

This is the affine, scheme-free form of the Jacobian roadmap's `Cl(X) ≅ Pic X` dictionary
(`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "the dictionaries `Cartier ≃ line
bundles` ... `Cl(X) ≅ Pic X`"), realized for the Dedekind model before the global Picard scheme
exists. It reuses Tau Ceti's `fractionalIdealDivisorAddEquiv` and `OrderSystem.ofDedekindDomain`
API and Mathlib's `ClassGroup R`, `ClassGroup.equiv` (independence of the fraction field) and
`QuotientAddGroup.congr`; no external mathematics is vendored.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]

/-- The isomorphism `fractionalIdealDivisorAddEquiv R K` between invertible fractional ideals and
Weil divisors carries the subgroup of principal fractional ideals onto the subgroup of principal
divisors: this is `fractionalIdealDivisorAddEquiv_toPrincipalIdeal` at the level of subgroups, and
it is exactly the compatibility needed to descend the isomorphism to the class groups. -/
private lemma map_toPrincipalIdeal_range :
    AddSubgroup.map (fractionalIdealDivisorAddEquiv R K).toAddMonoidHom
        (Subgroup.toAddSubgroup (toPrincipalIdeal R K).range) =
      (OrderSystem.ofDedekindDomain R K).principalSubgroup := by
  rw [(OrderSystem.ofDedekindDomain R K).principalSubgroup_eq_range,
    ← MonoidHom.coe_toAdditive_range, AddMonoidHom.map_range]
  refine congrArg _ (AddMonoidHom.ext fun x => ?_)
  rw [OrderSystem.principalHom_apply, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  exact fractionalIdealDivisorAddEquiv_toPrincipalIdeal (Additive.toMul x)

/-- **The divisor class group of the affine Dedekind curve is the ideal class group.**

For a Dedekind domain `R` with fraction field `K`, the Weil-divisor divisor class group
`(OrderSystem.ofDedekindDomain R K).ClassGroup` of the height-one spectrum is isomorphic to the
ideal class group `ClassGroup R`, via the isomorphism `fractionalIdealDivisorAddEquiv R K` of
invertible fractional ideals with Weil divisors descended to the quotient by principal
divisors/ideals. This is the affine `Cl(X) ≅ Pic X` of the Jacobian roadmap. See
`classGroupAddEquiv_divisorClass_fractionalIdealDivisor` and
`classGroupAddEquiv_symm_ofMul_mk` for the characterizing formulas. -/
noncomputable def classGroupAddEquiv :
    (OrderSystem.ofDedekindDomain R K).ClassGroup ≃+ Additive (ClassGroup R) :=
  (QuotientAddGroup.congr _ _ (fractionalIdealDivisorAddEquiv R K)
      (map_toPrincipalIdeal_range R K)).symm.trans
    (MulEquiv.toAdditive (ClassGroup.equiv K)).symm

variable {R K}

/-- The class group isomorphism sends the class of the Weil divisor of an invertible fractional
ideal `I` to the ideal class of `I`. Together with the surjectivity of `fractionalIdealDivisor`
and of `divisorClass` this pins down `classGroupAddEquiv` on every element. -/
@[simp]
lemma classGroupAddEquiv_divisorClass_fractionalIdealDivisor (I : (FractionalIdeal R⁰ K)ˣ) :
    classGroupAddEquiv R K
        ((OrderSystem.ofDedekindDomain R K).divisorClass
          (fractionalIdealDivisor R K (Additive.ofMul I)))
      = Additive.ofMul (ClassGroup.mk K I) := by
  erw [classGroupAddEquiv, AddEquiv.trans_apply,
    ← fractionalIdealDivisorAddEquiv_apply,
    OrderSystem.divisorClass_eq_mk']
  -- `QuotientAddGroup.congr` carries `mk' G' x` to `mk' H' (e x)` definitionally, but Mathlib's
  -- `QuotientGroup.congr_mk'` is not tagged `@[to_additive]`, so there is no additive lemma to
  -- rewrite with; exhibit the identity to expose an `e.symm (e _)` that `symm_apply_apply` cancels.
  rw [show (QuotientAddGroup.mk' (OrderSystem.ofDedekindDomain R K).principalSubgroup)
        (fractionalIdealDivisorAddEquiv R K (Additive.ofMul I))
      = (QuotientAddGroup.congr (Subgroup.toAddSubgroup (toPrincipalIdeal R K).range)
          (OrderSystem.ofDedekindDomain R K).principalSubgroup (fractionalIdealDivisorAddEquiv R K)
          (map_toPrincipalIdeal_range R K)) (QuotientAddGroup.mk' _ (Additive.ofMul I)) from rfl,
    AddEquiv.symm_apply_apply]
  -- `QuotientAddGroup.mk' (Subgroup.toAddSubgroup H) (Additive.ofMul x)` and
  -- `Additive.ofMul (QuotientGroup.mk' H x)` are the same term through the `Additive` type-tag on
  -- the quotient, but no rewrite lemma bridges the two `mk'`s, so reshape by `change` before
  -- applying `MulEquiv.toAdditive_apply_symm_apply`.
  change (MulEquiv.toAdditive (ClassGroup.equiv K)).symm
      (Additive.ofMul (QuotientGroup.mk' (toPrincipalIdeal R K).range I)) = _
  rw [MulEquiv.toAdditive_apply_symm_apply, MonoidHom.coe_toAdditive]
  -- `MonoidHom.coe_toAdditive` leaves `Additive.ofMul (… (Additive.toMul (Additive.ofMul _)))`;
  -- collapse the `toMul ∘ ofMul` type-tag round-trip (again a definitional identity with no
  -- applicable rewrite lemma) so the two sides differ only inside `Additive.ofMul`.
  change Additive.ofMul
      ((ClassGroup.equiv K).symm (QuotientGroup.mk' (toPrincipalIdeal R K).range I))
      = Additive.ofMul (ClassGroup.mk K I)
  congr 1
  rw [MulEquiv.symm_apply_eq, ClassGroup.equiv_mk]
  congr 1
  ext
  simp [Units.coe_mapEquiv, FractionalIdeal.canonicalEquiv_self]

/-- The inverse of the class group isomorphism sends the ideal class of an invertible fractional
ideal `I` to the divisor class of the Weil divisor of `I`. This is the canonical inverse formula,
dual to `classGroupAddEquiv_divisorClass_fractionalIdealDivisor`. -/
@[simp]
lemma classGroupAddEquiv_symm_ofMul_mk (I : (FractionalIdeal R⁰ K)ˣ) :
    (classGroupAddEquiv R K).symm (Additive.ofMul (ClassGroup.mk K I)) =
      (OrderSystem.ofDedekindDomain R K).divisorClass
        (fractionalIdealDivisor R K (Additive.ofMul I)) :=
  (classGroupAddEquiv R K).symm_apply_eq.mpr
    (classGroupAddEquiv_divisorClass_fractionalIdealDivisor I).symm

/-- The class group isomorphism on a general divisor class: the class of a Weil divisor `D` maps to
the ideal class of the invertible fractional ideal `∏_v v ^ (D v)` recovered from `D`. -/
lemma classGroupAddEquiv_divisorClass (D : WeilDivisor (HeightOneSpectrum R)) :
    classGroupAddEquiv R K ((OrderSystem.ofDedekindDomain R K).divisorClass D) =
      Additive.ofMul (ClassGroup.mk K (Additive.toMul
        ((fractionalIdealDivisorAddEquiv R K).symm D))) := by
  have hD : fractionalIdealDivisor R K
      (Additive.ofMul (Additive.toMul ((fractionalIdealDivisorAddEquiv R K).symm D))) = D := by
    rw [ofMul_toMul, ← fractionalIdealDivisorAddEquiv_apply, AddEquiv.apply_symm_apply]
  conv_lhs => rw [← hD]
  rw [classGroupAddEquiv_divisorClass_fractionalIdealDivisor]

/-- Non-vacuity: the class group isomorphism sends the class of the point divisor `[v]` of a
height-one prime `v` to the ideal class of `v`, viewed as an invertible fractional ideal. -/
lemma classGroupAddEquiv_divisorClass_ofPoint (v : HeightOneSpectrum R) :
    classGroupAddEquiv R K ((OrderSystem.ofDedekindDomain R K).divisorClass (ofPoint v)) =
      Additive.ofMul (ClassGroup.mk K
        (Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))) := by
  rw [← fractionalIdealDivisor_asIdeal (K := K) v,
    classGroupAddEquiv_divisorClass_fractionalIdealDivisor]

end WeilDivisor

end AlgebraicGeometry

end TauCeti
