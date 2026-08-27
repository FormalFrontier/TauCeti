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
used to identify cyclic discriminant forms, including the `Aₙ`, odd `Dₙ`, `E₆`, and `E₇`
root lattices.

## Main declarations

* `TauCeti.FiniteQuadraticModule.cyclicMap`: the quadratic map on `ZMod n` with generator value
  `a`.
* `TauCeti.FiniteQuadraticModule.cyclic`: the resulting finite quadratic module.
* `TauCeti.FiniteQuadraticModule.cyclicIsometryOfGenerator`: an additive equivalence matching
  generator values is an isometry.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.

This supplies the cyclic presented modules needed by Layer 5 of
`TauCetiRoadmap/IntegralLattices/README.md`.
-/

public section

namespace TauCeti

namespace FiniteQuadraticModule

variable (n : ℕ) (a : AddCircle (1 : ℚ))

/-! ## The presenting quadratic map on `ℤ` -/

/-- The bilinear map `(x, y) ↦ xya` on `ℤ`. -/
private def intBilin : LinearMap.BilinMap ℤ ℤ (AddCircle (1 : ℚ)) :=
  LinearMap.mk₂ ℤ (fun x y : ℤ ↦ (x * y) • a)
    (fun x y z ↦ by rw [add_mul, add_smul])
    (fun r x y ↦ by rw [smul_eq_mul, mul_assoc, mul_smul])
    (fun x y z ↦ by rw [mul_add, add_smul])
    (fun r x y ↦ by rw [smul_eq_mul, mul_left_comm, mul_smul])

/-- The quadratic map `x ↦ x²a` on `ℤ`. -/
private def intQuadratic : QuadraticMap ℤ ℤ (AddCircle (1 : ℚ)) :=
  (intBilin a).toQuadraticMap

/-- The two torsion hypotheses put the multiples of `n` in the quadratic radical. -/
private theorem zmultiples_le_radical_intQuadratic
    (hquad : ((n : ℤ) * n) • a = 0) (hpolar : (2 * (n : ℤ)) • a = 0) :
    (AddSubgroup.zmultiples (n : ℤ)).toIntSubmodule ≤ (intQuadratic a).radical := by
  intro x hx
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  constructor
  · change (((k * (n : ℤ)) * (k * n)) • a) = 0
    have hcoeff : (k * (n : ℤ)) * (k * n) = (k * k) * (n * n) := by ring
    rw [hcoeff, mul_smul, hquad, smul_zero]
  · apply LinearMap.ext
    intro y
    -- Unfolding the polar of `toQuadraticMap` exposes the two bilinear evaluations.
    change QuadraticMap.polar (intQuadratic a) (k • (n : ℤ)) y = 0
    rw [intQuadratic, LinearMap.BilinMap.polar_toQuadraticMap]
    simp only [intBilin, LinearMap.mk₂_apply, smul_eq_mul]
    change ((k * (n : ℤ) * y) • a) + ((y * (k * n)) • a) = 0
    rw [← add_smul]
    have hcoeff : k * (n : ℤ) * y + y * (k * n) = (k * y) * (2 * n) := by ring
    rw [hcoeff, mul_smul, hpolar, smul_zero]

/-- The quotient of `ℤ` by the multiples of `n`, as an integer-linear equivalence with
`ZMod n`. -/
private def intQuotientEquivZMod :
    (ℤ ⧸ (AddSubgroup.zmultiples (n : ℤ)).toIntSubmodule) ≃ₗ[ℤ] ZMod n :=
  { Int.quotientZMultiplesNatEquivZMod n with
    map_smul' := by
      intro k x
      convert! (Int.quotientZMultiplesNatEquivZMod n).toAddMonoidHom.map_zsmul k x using 1 }

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
  rw [← zsmul_one, (cyclicMap n a hquad hpolar).map_smul]
  congr 1
  unfold cyclicMap
  rw [QuadraticMap.comp_apply]
  have he : (intQuotientEquivZMod n).symm 1 = Submodule.Quotient.mk (1 : ℤ) := by
    apply (intQuotientEquivZMod n).injective
    rw [LinearEquiv.apply_symm_apply]
    have hs : (QuotientAddGroup.quotientAddEquivOfEq (ZMod.ker_intCastAddHom n)).symm
        (QuotientAddGroup.mk 1) = QuotientAddGroup.mk 1 := by
      apply (QuotientAddGroup.quotientAddEquivOfEq (ZMod.ker_intCastAddHom n)).injective
      rw [AddEquiv.apply_symm_apply, QuotientAddGroup.quotientAddEquivOfEq_mk]
    -- Expose the composition defining the quotient-to-`ZMod` equivalence.
    change (1 : ZMod n) = Int.quotientZMultiplesNatEquivZMod n (QuotientAddGroup.mk 1)
    rw [Int.quotientZMultiplesNatEquivZMod, AddEquiv.trans_apply, hs]
    change (1 : ZMod n) = ((1 : ℤ) : ZMod n)
    simp
  -- Expose the lifted quadratic map at the quotient representative.
  change (intQuadratic a).lift (AddSubgroup.zmultiples (n : ℤ)).toIntSubmodule _
    ((intQuotientEquivZMod n).symm 1) = a
  rw [he, QuadraticMap.lift_mk]
  simp [intQuadratic, intBilin]

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

variable [NeZero n]

/-- **The finite quadratic module on `ZMod n` whose standard generator has value `a`.**

The nonzero-modulus hypothesis is exactly what makes `ZMod n` finite. -/
@[expose] noncomputable def cyclic : FiniteQuadraticModule where
  toFiniteBilinearModule := {
    carrier := ZMod n
    pairing := LinearMap.toAddMonoidHom'.comp
      (cyclicMap n a hquad hpolar).polarBilin.toAddMonoidHom
    pairing_comm := fun x y ↦ QuadraticMap.polar_comm (cyclicMap n a hquad hpolar) x y }
  quadratic := cyclicMap n a hquad hpolar
  polar_eq_pairing' := fun _ _ ↦ (rfl)

@[simp]
theorem cyclic_quadratic (x : ZMod n) :
    (cyclic n a hquad hpolar).quadratic x = cyclicMap n a hquad hpolar x := (rfl)

@[simp]
theorem cyclic_pairing (x y : ZMod n) :
    (cyclic n a hquad hpolar).toFiniteBilinearModule.pairing x y =
      QuadraticMap.polar (cyclicMap n a hquad hpolar) x y := (rfl)

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
    -- Identify the bundled linear equivalence with its underlying additive equivalence.
    change r (e (k : ZMod n)) = q (k : ZMod n)
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
