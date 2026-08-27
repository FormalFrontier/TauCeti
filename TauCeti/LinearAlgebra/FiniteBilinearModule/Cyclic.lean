/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Finite quadratic modules on cyclic groups

A `ℚ/ℤ`-valued quadratic map on `ZMod n` is determined by its value `a` on the standard
generator.  Conversely, a value `a : ℚ/ℤ` defines such a map when

```text
n²a = 0,   2na = 0.
```

Indeed, the quadratic map `k ↦ k²a` on `ℤ` descends modulo `n` exactly when translation by `n`
does not change its values or its polar form.  This file carries out that quotient construction
and, for nonzero `n`, packages it as `TauCeti.FiniteQuadraticModule.cyclic`.

The companion `TauCeti.FiniteQuadraticModule.cyclicIsometryOfGenerator` shows that an additive
equivalence out of `ZMod n` which matches the quadratic values of the standard generators is
automatically an isometry.  Together these declarations give the shared presented-module API
used to identify cyclic discriminant forms; the `E₆` and `E₇` root lattices are identified this
way, and the `Aₙ` and odd `Dₙ` rows are intended to follow.

## Main declarations

* `TauCeti.FiniteQuadraticModule.cyclicMap`: the quadratic map on `ZMod n` with generator value
  `a`.
* `TauCeti.FiniteQuadraticModule.cyclic`: the resulting finite quadratic module.
* `TauCeti.FiniteQuadraticModule.cyclicIsometryOfGenerator`: an additive equivalence matching
  generator values is an isometry.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* The quotient construction and the generator-isometry argument below are promoted, essentially
  unchanged, from the private `E₆`/`E₇` scaffolding formerly in
  `TauCeti/LinearAlgebra/IntegralLattice/RootLattice/TypeE.lean`.

This supplies the cyclic presented modules needed by Layer 5 of
`TauCetiRoadmap/IntegralLattices/README.md`.
-/

public section

namespace TauCeti

namespace FiniteQuadraticModule

variable (n : ℕ) (a : AddCircle (1 : ℚ))

/-! ## The presenting quadratic map on `ℤ` -/

/-- The quadratic map `x ↦ x²a` on `ℤ`, as the squaring map followed by multiplication by `a`. -/
private def intQuadratic : QuadraticMap ℤ ℤ (AddCircle (1 : ℚ)) :=
  (LinearMap.toSpanSingleton ℤ (AddCircle (1 : ℚ)) a).compQuadraticMap (QuadraticMap.sq (R := ℤ))

private theorem intQuadratic_apply (x : ℤ) : intQuadratic a x = (x * x) • a := by
  rw [intQuadratic, LinearMap.compQuadraticMap_apply, QuadraticMap.sq_apply,
    LinearMap.toSpanSingleton_apply]

private theorem polar_intQuadratic (x y : ℤ) :
    QuadraticMap.polar (intQuadratic a) x y = (2 * (x * y)) • a := by
  rw [QuadraticMap.polar, intQuadratic_apply, intQuadratic_apply, intQuadratic_apply,
    ← sub_smul, ← sub_smul]
  congr 1
  ring

/-- The two torsion hypotheses put the multiples of `n` in the quadratic radical. -/
private theorem zmultiples_le_radical_intQuadratic
    (hquad : ((n : ℤ) * n) • a = 0) (hpolar : (2 * (n : ℤ)) • a = 0) :
    (AddSubgroup.zmultiples (n : ℤ)).toIntSubmodule ≤ (intQuadratic a).radical := by
  intro x hx
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  constructor
  · rw [intQuadratic_apply, smul_eq_mul]
    have hcoeff : (k * (n : ℤ)) * (k * n) = (k * k) * (n * n) := by ring
    rw [hcoeff, mul_smul, hquad, smul_zero]
  · refine LinearMap.ext fun y ↦ ?_
    rw [LinearMap.zero_apply, QuadraticMap.polarBilin_apply_apply, polar_intQuadratic,
      smul_eq_mul]
    have hcoeff : 2 * (k * (n : ℤ) * y) = (k * y) * (2 * n) := by ring
    rw [hcoeff, mul_smul, hpolar, smul_zero]

/-- The quotient of `ℤ` by the multiples of `n`, as an integer-linear equivalence with
`ZMod n`. -/
private def intQuotientEquivZMod :
    (ℤ ⧸ (AddSubgroup.zmultiples (n : ℤ)).toIntSubmodule) ≃ₗ[ℤ] ZMod n :=
  (Int.quotientZMultiplesNatEquivZMod n).toIntLinearEquiv

/-- The quotient equivalence sends the class of an integer to its reduction.

This is the sole point at which the construction of `Int.quotientZMultiplesNatEquivZMod` is used:
it is a kernel lift, so it computes on quotient representatives. -/
private theorem intQuotientEquivZMod_mk (k : ℤ) :
    intQuotientEquivZMod n (Submodule.Quotient.mk k) = (k : ZMod n) := rfl

/-- The inverse quotient equivalence sends an integer class to its quotient representative. -/
private theorem intQuotientEquivZMod_symm_intCast (k : ℤ) :
    (intQuotientEquivZMod n).symm (k : ZMod n) = Submodule.Quotient.mk k := by
  rw [← intQuotientEquivZMod_mk, LinearEquiv.symm_apply_apply]

/-! ## The cyclic quadratic module -/

variable (hquad : ((n : ℤ) * n) • a = 0) (hpolar : (2 * (n : ℤ)) • a = 0)

include hquad hpolar

/-- The quadratic map on `ZMod n` whose standard generator has value `a`.

The hypotheses `n²a = 0` and `2na = 0` say respectively that the proposed quadratic values and
polar pairing are well defined modulo `n`. -/
noncomputable def cyclicMap : QuadraticMap ℤ (ZMod n) (AddCircle (1 : ℚ)) :=
  ((intQuadratic a).lift (AddSubgroup.zmultiples (n : ℤ)).toIntSubmodule
      (zmultiples_le_radical_intQuadratic n a hquad hpolar)).comp
    (intQuotientEquivZMod n).symm.toLinearMap

/-- The value of `cyclicMap` on the reduction of an integer. -/
@[simp]
theorem cyclicMap_intCast (k : ℤ) :
    cyclicMap n a hquad hpolar (k : ZMod n) = (k * k) • a := by
  unfold cyclicMap
  rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe, intQuotientEquivZMod_symm_intCast,
    QuadraticMap.lift_mk, intQuadratic_apply]

/-- The standard generator of `cyclicMap` has value `a`. -/
@[simp]
theorem cyclicMap_one : cyclicMap n a hquad hpolar 1 = a := by
  simpa using cyclicMap_intCast n a hquad hpolar 1

/-- The polar pairing of two integer classes is `2kla`. -/
@[simp]
theorem polar_cyclicMap_intCast (k l : ℤ) :
    QuadraticMap.polar (cyclicMap n a hquad hpolar) (k : ZMod n) (l : ZMod n) =
      (2 * (k * l)) • a := by
  rw [QuadraticMap.polar, ← Int.cast_add, cyclicMap_intCast, cyclicMap_intCast,
    cyclicMap_intCast, ← sub_smul, ← sub_smul]
  congr 1
  ring

/-- The standard generator of `cyclicMap` pairs with itself to `2a`.

This is deliberately not a `simp` lemma: `QuadraticMap.polar_self` and `cyclicMap_one` already
rewrite the left-hand side, so it is stated only for the `ℤ`-scalar form shared with
`polar_cyclicMap_intCast`. -/
theorem polar_cyclicMap_one_one :
    QuadraticMap.polar (cyclicMap n a hquad hpolar) 1 1 = (2 : ℤ) • a := by
  simpa using polar_cyclicMap_intCast n a hquad hpolar 1 1

variable [NeZero n]

/-- **The finite quadratic module on `ZMod n` whose standard generator has value `a`.**

The nonzero-modulus hypothesis is exactly what makes `ZMod n` finite. -/
@[expose] noncomputable def cyclic : FiniteQuadraticModule :=
  ofQuadraticMap (ZMod n) (cyclicMap n a hquad hpolar)

@[simp]
theorem cyclic_quadratic (x : ZMod n) :
    (cyclic n a hquad hpolar).quadratic x = cyclicMap n a hquad hpolar x :=
  ofQuadraticMap_quadratic _ _ x

@[simp]
theorem cyclic_pairing (x y : ZMod n) :
    (cyclic n a hquad hpolar).toFiniteBilinearModule.pairing x y =
      QuadraticMap.polar (cyclicMap n a hquad hpolar) x y :=
  ofQuadraticMap_pairing _ _ x y

omit hquad hpolar [NeZero n] in
/-- **An additive equivalence from `ZMod n` matching the generator values is an isometry.**

Both forms are stated as bare quadratic maps so that the construction applies before either is
packaged as a finite quadratic module. -/
noncomputable def cyclicIsometryOfGenerator {A : Type*} [AddCommGroup A]
    (q : QuadraticMap ℤ (ZMod n) (AddCircle (1 : ℚ)))
    (r : QuadraticMap ℤ A (AddCircle (1 : ℚ))) (e : ZMod n ≃+ A)
    (he : r (e 1) = q 1) : q.IsometryEquiv r where
  toLinearEquiv := e.toIntLinearEquiv
  map_app' x := by
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
    simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv]
    rw [← zsmul_one, map_zsmul, r.map_smul, q.map_smul, he]

omit hquad hpolar [NeZero n] in
@[simp]
theorem cyclicIsometryOfGenerator_toAddEquiv {A : Type*} [AddCommGroup A]
    (q : QuadraticMap ℤ (ZMod n) (AddCircle (1 : ℚ)))
    (r : QuadraticMap ℤ A (AddCircle (1 : ℚ))) (e : ZMod n ≃+ A)
    (he : r (e 1) = q 1) :
    (cyclicIsometryOfGenerator n q r e he).toAddEquiv = e := (rfl)

omit hquad hpolar [NeZero n] in
@[simp]
theorem cyclicIsometryOfGenerator_apply {A : Type*} [AddCommGroup A]
    (q : QuadraticMap ℤ (ZMod n) (AddCircle (1 : ℚ)))
    (r : QuadraticMap ℤ A (AddCircle (1 : ℚ))) (e : ZMod n ≃+ A)
    (he : r (e 1) = q 1) (x : ZMod n) :
    cyclicIsometryOfGenerator n q r e he x = e x := (rfl)

end FiniteQuadraticModule

end TauCeti
